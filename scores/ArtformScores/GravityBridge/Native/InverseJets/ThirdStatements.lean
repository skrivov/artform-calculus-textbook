import ArtformScores.GravityBridge.Native.InverseJets.ThirdDefs

/-! # Ordered noncommutative inverse jets through third order -/

namespace Artform.Scores.GravityBridge.Native.InverseJets.Statement

open Matrix

/-- **GAC2:ordered-third-inverse-jets**
(ordered noncommutative inverse jets through third order). -/
@[ledger "GAC2:ordered-third-inverse-jets"]
def thirdLaw : Prop :=
  ∀ (R : Type) [Ring R],
    (∀ (N0 N1 N2 N3 H : R) (_hNH : N0 * H = 1),
    N0 * inverseJet1 H N1 + N1 * H = 0 ∧
    N0 * inverseJet2 H N1 N2 + N1 * inverseJet1 H N1 + N2 * H = 0 ∧
    N0 * inverseJet3 H N1 N2 N3 + N1 * inverseJet2 H N1 N2 +
      N2 * inverseJet1 H N1 + N3 * H = 0) ∧
    (∀ (N0 N1 N2 N3 H : R) (_hHN : H * N0 = 1),
    inverseJet1 H N1 * N0 + H * N1 = 0 ∧
    inverseJet2 H N1 N2 * N0 + inverseJet1 H N1 * N1 + H * N2 = 0 ∧
    inverseJet3 H N1 N2 N3 * N0 + inverseJet2 H N1 N2 * N1 +
      inverseJet1 H N1 * N2 + H * N3 = 0) ∧
    (∀ (N0 N1 N2 N3 H X : R) (_hHN : H * N0 = 1)
    (_hNH : N0 * H = 1)
    (_hx : N0 * X + N1 * inverseJet2 H N1 N2 + N2 * inverseJet1 H N1 + N3 * H = 0),
    X = inverseJet3 H N1 N2 N3) ∧
    (∀ (l p q : ℚ),
    signedN0 * thirdH l p q + firstN l p q * secondH l p q +
      secondN l p q * firstH l p q + thirdN l p q * signedH0 = 0) ∧
    (∀ (l p q : ℚ),
    linkCube l p q = (1 / 4 : ℚ) • linkD (l ^ 3) (p ^ 3) (q ^ 3)) ∧
    (∀ (l p q : ℚ),
    thirdN l p q = thirdLinkProduct l p q)

end Artform.Scores.GravityBridge.Native.InverseJets.Statement
