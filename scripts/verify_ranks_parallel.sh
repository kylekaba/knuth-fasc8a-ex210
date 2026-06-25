#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
make -s all
export OMP_NUM_THREADS="${OMP_NUM_THREADS:-1}"
JOBS="${JOBS:-6}"
run() {
  name="$1"; matrix="$2"; cert="$3"; eig="$4"
  mkdir -p build/verify-logs
  build/bin/verify_rank_cert "$matrix" "$cert" "$eig" \
    >"build/verify-logs/${name}.out" 2>"build/verify-logs/${name}.err"
  echo "PASS $name"
}
export -f run
export ROOT
printf '%s\0' \
  'Trel_plus|data/blocks/Trel_plus.kmc|data/certs/Trel_plus_border.kwc2|data/certs/Trel_plus_eigen50.vec' \
  'Trel_minus|data/blocks/Trel_minus.kmc|data/certs/Trel_minus_shift50.kwc2|-' \
  'U1_plus|data/blocks/U1_plus.kmc|data/certs/U1_plus_shift50.kwc2|-' \
  'U1_minus|data/blocks/U1_minus.kmc|data/certs/U1_minus_shift50.kwc2|-' \
  'U2_plus|data/blocks/U2_plus.kmc|data/certs/U2_plus_shift50.kwc2|-' \
  'U2_minus|data/blocks/U2_minus.kmc|data/certs/U2_minus_shift50.kwc2|-' \
| xargs -0 -n1 -P "$JOBS" bash -c '
    IFS="|" read -r a b c d <<< "$1"
    run "$a" "$b" "$c" "$d"
  ' _
echo "ALL SIX EXACT RANK CERTIFICATES PASS"
