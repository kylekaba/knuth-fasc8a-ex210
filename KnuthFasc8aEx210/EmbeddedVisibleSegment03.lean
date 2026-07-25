import KnuthFasc8aEx210.EmbeddedCertificateData

namespace KnuthFasc8aEx210

/-- The final bounded segment of the checked-in visible Horner replay. -/
theorem embeddedVisibleSegment03_eq_zero :
    checkedVisibleHornerSegmentBad embeddedTallBytes embeddedTallHeader
      embeddedVisiblePolynomial embeddedTallFinish embeddedVisibleHorner 3 = 0 := by
  native_decide

end KnuthFasc8aEx210
