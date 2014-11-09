import Nominal
import Theory

module Theories.Contexts {i} (N : Nominal.struct) (T : Theory.struct {i}) where
  module N = Nominal.struct N
  module T = Theory.struct T

  data term : Set i where
    · : term
    _,_∶_ : term → N.name → T.judgement → term

  data judgement : Set i where
    _ctx : term → judgement
    _∉_ : N.name → term → judgement
    _∋_∶_ : term → N.name → T.judgement → judgement
    _≤_ : term → term → judgement

  infixl 8 _ctx
  infixr 8 _∉_
  infixr 8 _∋_∶_
  infixr 8 _≤_

  data ⟦_⟧ : judgement → Set i where
    ·-ctx : ⟦ · ctx ⟧
    Γ,x∶J-ctx : ∀ {Γ x J}
      → ⟦ Γ ctx ⟧
      → ⟦ x ∉ Γ ⟧
      → ⟦ Γ , x ∶ J ctx ⟧

    x∉· : ∀ {x}
      → ⟦ x ∉ · ⟧
    x∉Γ,y∶J : ∀ {Γ x y J}
      → x N.≠ y
      → ⟦ x ∉ Γ , y ∶ J ⟧

    Γ,x∶J∋x∶J : ∀ {Γ x J}
      → ⟦ (Γ , x ∶ J) ∋ x ∶ J ⟧

    Γ,y∶J′∋x∶J : ∀ {Γ x y J J′}
      → ⟦ Γ ∋ x ∶ J ⟧
      → ⟦ (Γ , y ∶ J′) ∋ x ∶ J ⟧

    ·≤Γ : ∀ {Γ}
      → ⟦ · ≤ Γ ⟧

    Γ,x∶J≤Δ : ∀ {Γ x J Δ}
      → ⟦ Γ ≤ Δ ⟧
      → ⟦ Δ ∋ x ∶ J ⟧
      → ⟦ Γ , x ∶ J ≤ Δ ⟧

  theory : Theory.struct {i}
  theory = record { term = term ; judgement = judgement ; ⟦_⟧ = ⟦_⟧ }
