import Nominal

module theories-with-judgement (N : Nominal.struct) where
  open import Theories.Logic N as L
    using (⊤; ⊥; _⊃_)
  open import Theories.Contexts N L.theory hiding (⟦_⟧)
  open import Theories.SCTT N

  module example {x} where
    ex₁ : ⟦ λ⟨ x ⟩ abort var⟨ x ⟩ ∈ ⊥ ⊃ ⊤ [ · ] ⟧
    ex₁ =
      ⊃-member-eq⟨ x ⟩
      ⊥-elim-eq
      hyp-eq⟨ x ⟩ {{Γ,x∶J∋x∶J}} {{·≤Γ}}

    ex₂ : ⟦ ⊥ ⊃ ⊤ true-[ · ] ⟧
    ex₂ =
      ⊃-intro⟨ x ⟩
      ⊥-elim
      hyp⟨ x ⟩ {{Γ,x∶J∋x∶J}} {{·≤Γ}}

    ex₃ : ⟦ ⊥ ⊃ ⊤ true-[ · ] ⟧
    ex₃ =
      witness⟨
        λ⟨ x ⟩ abort var⟨ x ⟩
      ⟩ ex₁
