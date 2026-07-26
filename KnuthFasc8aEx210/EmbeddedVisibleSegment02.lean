import KnuthFasc8aEx210.EmbeddedCertificateData

namespace KnuthFasc8aEx210

/-- The third bounded segment of the checked-in visible Horner replay. -/
theorem embeddedVisibleSegment02_eq_zero :
    checkedVisibleHornerSegmentBad embeddedTallBytes embeddedTallHeader
      embeddedVisiblePolynomial embeddedTallFinish embeddedVisibleHorner 2 = 0 := by
  native_decide

end KnuthFasc8aEx210
