import KnuthFasc8aEx210.EmbeddedCertificateData

namespace KnuthFasc8aEx210

/-- The first bounded segment of the checked-in visible Horner replay. -/
theorem embeddedVisibleSegment00_eq_zero :
    checkedVisibleHornerSegmentBad embeddedTallBytes embeddedTallHeader
      embeddedVisiblePolynomial embeddedTallFinish embeddedVisibleHorner 0 = 0 := by
  native_decide

end KnuthFasc8aEx210
