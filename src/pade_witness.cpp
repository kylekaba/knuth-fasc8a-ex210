#include <algorithm>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

static constexpr uint32_t P = 101;

struct E {
  uint8_t a, b;
};

static uint8_t invp[101];

static inline bool operator==(E x, E y) { return x.a == y.a && x.b == y.b; }
static inline bool zero(E x) { return x.a == 0 && x.b == 0; }
static inline E add(E x, E y) {
  uint16_t a = x.a + y.a, b = x.b + y.b;
  return {(uint8_t)(a >= P ? a - P : a), (uint8_t)(b >= P ? b - P : b)};
}
static inline E sub(E x, E y) {
  return {(uint8_t)(x.a >= y.a ? x.a - y.a : x.a + P - y.a),
          (uint8_t)(x.b >= y.b ? x.b - y.b : x.b + P - y.b)};
}
static inline E mul(E x, E y) {
  uint32_t a = (uint32_t)x.a * y.a + 2u * (uint32_t)x.b * y.b;
  uint32_t b = (uint32_t)x.a * y.b + (uint32_t)x.b * y.a;
  return {(uint8_t)(a % P), (uint8_t)(b % P)};
}
static inline E inv(E x) {
  uint32_t d = ((uint32_t)x.a * x.a + P - 2u * (uint32_t)x.b * x.b % P) % P;
  if (!d) throw std::runtime_error("inverse zero");
  uint32_t q = invp[d];
  return {(uint8_t)(x.a * q % P), (uint8_t)(x.b ? (P - x.b) * q % P : 0)};
}
static inline E divide(E x, E y) { return mul(x, inv(y)); }

using Poly = std::vector<E>;

static void trim(Poly &p) {
  while (!p.empty() && zero(p.back())) p.pop_back();
}

static Poly poly_sub(const Poly &x, const Poly &y) {
  Poly out(std::max(x.size(), y.size()));
  for (size_t i = 0; i < out.size(); ++i) {
    E a = i < x.size() ? x[i] : E{0, 0};
    E b = i < y.size() ? y[i] : E{0, 0};
    out[i] = sub(a, b);
  }
  trim(out);
  return out;
}

static Poly poly_mul(const Poly &x, const Poly &y) {
  if (x.empty() || y.empty()) return {};
  Poly out(x.size() + y.size() - 1, E{0, 0});
  for (size_t i = 0; i < x.size(); ++i)
    for (size_t j = 0; j < y.size(); ++j)
      out[i + j] = add(out[i + j], mul(x[i], y[j]));
  trim(out);
  return out;
}

static std::pair<Poly, Poly> poly_divmod(Poly numerator, const Poly &denominator) {
  if (denominator.empty()) throw std::runtime_error("polynomial division by zero");
  if (numerator.size() < denominator.size()) return {{}, std::move(numerator)};
  Poly quotient(numerator.size() - denominator.size() + 1, E{0, 0});
  E denominator_lead_inv = inv(denominator.back());
  while (!numerator.empty() && numerator.size() >= denominator.size()) {
    size_t shift = numerator.size() - denominator.size();
    E factor = mul(numerator.back(), denominator_lead_inv);
    quotient[shift] = factor;
    for (size_t j = 0; j < denominator.size(); ++j)
      numerator[shift + j] = sub(numerator[shift + j], mul(factor, denominator[j]));
    trim(numerator);
  }
  trim(quotient);
  return {std::move(quotient), std::move(numerator)};
}

static Poly poly_scale(Poly p, E c) {
  for (E &x : p) x = mul(c, x);
  trim(p);
  return p;
}

static uint64_t fnv64(const std::string &path) {
  std::ifstream f(path, std::ios::binary);
  if (!f) throw std::runtime_error("open " + path);
  uint64_t h = 1469598103934665603ULL;
  char bytes[65536];
  while (f) {
    f.read(bytes, sizeof bytes);
    std::streamsize n = f.gcount();
    for (std::streamsize i = 0; i < n; ++i) {
      h ^= (uint8_t)bytes[i];
      h *= 1099511628211ULL;
    }
  }
  return h;
}

#pragma pack(push, 1)
struct CertHeader {
  char magic[8];
  uint32_t version, prime, nonresidue, n, lambda, border, pivot, terms, bm_terms, degree;
  uint64_t seed, matrix_hash, eigen_hash;
};

struct WitnessHeader {
  char magic[8];
  uint32_t version, prime, nonresidue, degree, u_length, v_length;
  uint64_t certificate_hash;
};
#pragma pack(pop)

struct Certificate {
  CertHeader header;
  Poly moments;
  Poly denominator;
};

static Certificate load_certificate(const std::string &path) {
  std::ifstream f(path, std::ios::binary);
  if (!f) throw std::runtime_error("open " + path);
  Certificate c{};
  f.read((char *)&c.header, sizeof c.header);
  if (!f || std::string(c.header.magic, 8) != "KMW2CERT" || c.header.version != 2 ||
      c.header.prime != P || c.header.nonresidue != 2 || c.header.degree != c.header.n ||
      c.header.bm_terms != 2 * c.header.n || c.header.terms < c.header.bm_terms)
    throw std::runtime_error("bad certificate header");
  c.moments.resize(c.header.terms);
  c.denominator.resize(c.header.degree + 1);
  f.read((char *)c.moments.data(), 2 * c.moments.size());
  f.read((char *)c.denominator.data(), 2 * c.denominator.size());
  char trailing;
  if (!f || f.read(&trailing, 1)) throw std::runtime_error("bad certificate payload");
  for (E x : c.moments) if (x.a >= P || x.b >= P) throw std::runtime_error("noncanonical moment");
  for (E x : c.denominator) if (x.a >= P || x.b >= P) throw std::runtime_error("noncanonical denominator");
  return c;
}

static Poly pade_numerator(const Certificate &c) {
  size_t n = c.header.degree;
  Poly r(n, E{0, 0});
  for (size_t k = 0; k < n; ++k)
    for (size_t j = 0; j <= k; ++j)
      r[k] = add(r[k], mul(c.denominator[j], c.moments[k - j]));
  trim(r);
  return r;
}

static std::pair<Poly, Poly> extended_gcd(const Poly &d, const Poly &r) {
  Poly r0 = d, r1 = r;
  Poly u0{{1, 0}}, u1;
  Poly v0, v1{{1, 0}};
  size_t iteration = 0;
  while (!r1.empty()) {
    auto [q, remainder] = poly_divmod(r0, r1);
    Poly u2 = poly_sub(u0, poly_mul(q, u1));
    Poly v2 = poly_sub(v0, poly_mul(q, v1));
    r0 = std::move(r1);
    r1 = std::move(remainder);
    u0 = std::move(u1);
    u1 = std::move(u2);
    v0 = std::move(v1);
    v1 = std::move(v2);
    if ((++iteration % 5000) == 0)
      std::cerr << "euclid iterations " << iteration << " remainder_degree "
                << (r1.empty() ? -1 : (int64_t)r1.size() - 1) << "\n";
  }
  if (r0.size() != 1 || zero(r0[0])) throw std::runtime_error("denominator and numerator not coprime");
  E scale = inv(r0[0]);
  return {poly_scale(std::move(u0), scale), poly_scale(std::move(v0), scale)};
}

static void verify_bezout(const Poly &d, const Poly &r, const Poly &u, const Poly &v) {
  Poly lhs = poly_sub(poly_mul(u, d), poly_scale(poly_mul(v, r), E{100, 0}));
  // `x - (-y)` above is addition; this avoids a second dedicated polynomial-add routine.
  trim(lhs);
  if (lhs.size() != 1 || !(lhs[0] == E{1, 0}))
    throw std::runtime_error("Bézout identity verification failed");
}

static void save_witness(const std::string &path, uint32_t degree, uint64_t certificate_hash,
                         const Poly &u, const Poly &v) {
  WitnessHeader h{};
  std::memcpy(h.magic, "KPB101W1", 8);
  h.version = 1;
  h.prime = P;
  h.nonresidue = 2;
  h.degree = degree;
  h.u_length = (uint32_t)u.size();
  h.v_length = (uint32_t)v.size();
  h.certificate_hash = certificate_hash;
  std::ofstream f(path, std::ios::binary);
  if (!f) throw std::runtime_error("write " + path);
  f.write((char *)&h, sizeof h);
  f.write((char *)u.data(), 2 * u.size());
  f.write((char *)v.data(), 2 * v.size());
  if (!f) throw std::runtime_error("write failed");
}

int main(int argc, char **argv) {
  for (int a = 1; a < 101; ++a)
    for (int b = 1; b < 101; ++b)
      if (a * b % 101 == 1) { invp[a] = b; break; }
  if (argc != 3) {
    std::cerr << "usage: pade_witness CERTIFICATE.kwc2 WITNESS.kpw1\n";
    return 1;
  }
  try {
    Certificate c = load_certificate(argv[1]);
    std::cerr << "computing numerator degree " << c.header.degree << "\n";
    Poly r = pade_numerator(c);
    std::cerr << "extended gcd denominator_degree " << c.denominator.size() - 1
              << " numerator_degree " << (r.empty() ? -1 : (int64_t)r.size() - 1) << "\n";
    auto [u, v] = extended_gcd(c.denominator, r);
    std::cerr << "witness lengths U=" << u.size() << " V=" << v.size() << "\n";
    verify_bezout(c.denominator, r, u, v);
    save_witness(argv[2], c.header.degree, fnv64(argv[1]), u, v);
    std::cout << "PASS wrote " << argv[2] << "\n";
    return 0;
  } catch (const std::exception &e) {
    std::cerr << "ERROR " << e.what() << "\n";
    return 2;
  }
}
