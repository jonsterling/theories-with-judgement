import Nominal

module Theories.Logic (N : Nominal.struct) where
  import Theory

  data term : Set where
    ⊤ ⊥ : term
    _⊃_ : term → term → term

  theory : Theory.struct

  open import Theories.Contexts N theory as Ctxt
    using (_ctx; _∋_∶_; ·; _,_∶_; _≤_)

  data judgement : Set where
    _true-[_] : term → Ctxt.term → judgement
  infixl 9 _true-[_]

  data ⟦_⟧ : judgement → Set
  theory = record { term = term ; judgement = judgement ; ⟦_⟧ = ⟦_⟧ }

  data ⟦_⟧ where
    ⊤-intro : ∀ {Γ}
          ⦃ _ : Ctxt.⟦ Γ ctx ⟧ ⦄
      → ⟦ ⊤ true-[ Γ ] ⟧

    ⊥-elim : ∀ {Γ P}
          ⦃ _ : Ctxt.⟦ Γ ctx ⟧ ⦄
      → ⟦ ⊥ true-[ Γ ] ⟧
      → ⟦ P true-[ Γ ] ⟧

    ⊃-intro⟨_⟩ : ∀ x {Γ P Q}
          ⦃ _ : Ctxt.⟦ Γ ctx ⟧ ⦄
      → ⟦ Q true-[ Γ , x ∶ (P true-[ Γ ]) ] ⟧
      → ⟦ P ⊃ Q true-[ Γ ] ⟧

    ⊃-elim : ∀ {Γ P Q}
          ⦃ _ : Ctxt.⟦ Γ ctx ⟧ ⦄
      → ⟦ P ⊃ Q true-[ Γ ] ⟧
      → ⟦ P true-[ Γ ] ⟧
      → ⟦ Q true-[ Γ ] ⟧

    hyp⟨_⟩ : ∀ x {Γ Δ P}
         ⦃ _ : Ctxt.⟦ Γ ctx ⟧ ⦄
         ⦃ _ : Ctxt.⟦ Γ ∋ x ∶ (P true-[ Δ ]) ⟧ ⦄
         ⦃ _ : Ctxt.⟦ Δ ≤ Γ ⟧ ⦄
      → ⟦ P true-[ Γ ] ⟧
