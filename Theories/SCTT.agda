-- "Simple Computational Type Theory"

import Nominal

module Theories.SCTT (N : Nominal.struct) where
  module N = Nominal.struct N

  import Theory
  open import Theories.Logic N as L
    using (⊤; ⊥; _⊃_; _true-[_])

  data term : Set where
    • : term
    λ⟨_⟩_ : N.name → term → term
    abort_ : term → term
    var⟨_⟩ : N.name → term
    app : term → term → term
  

  open import Theories.Contexts N L.theory as Ctxt
    using (_ctx; _∋_∶_; ·; _,_∶_; _≤_)
  
  data judgement : Set where
    _==_∈_[_] : term → term → L.term → Ctxt.term → judgement
    _true-[_] : L.term → Ctxt.term → judgement

  infixl 8 _==_∈_[_]
  infixl 8 _∈_[_]
  infixl 8 _true-[_]

  _∈_[_] : term → L.term → Ctxt.term → judgement
  M ∈ A [ Γ ] = M == M ∈ A [ Γ ]

  data ⟦_⟧ : judgement → Set where
    eq-sym_ : ∀ {Γ M N A}
      → ⟦ M == N ∈ A [ Γ ] ⟧
      → ⟦ N == M ∈ A [ Γ ] ⟧

    eq-trans : ∀ {Γ M N O A}
      → ⟦ M == N ∈ A [ Γ ] ⟧
      → ⟦ N == O ∈ A [ Γ ] ⟧
      → ⟦ M == O ∈ A [ Γ ] ⟧

    ⊤-intro : ∀ {Γ}
      → ⟦ ⊤ true-[ Γ ] ⟧
    ⊤-member-eq : ∀ {Γ}
      → ⟦ • ∈ ⊤ [ Γ ] ⟧

    ⊥-elim_ : ∀ {Γ P}
      → ⟦ ⊥ true-[ Γ ] ⟧
      → ⟦ P true-[ Γ ] ⟧
    ⊥-elim-eq_ : ∀ {Γ M N P}
      → ⟦ M == N ∈ ⊥ [ Γ ] ⟧
      → ⟦ abort M == abort N ∈ P [ Γ ] ⟧

    ⊃-intro⟨_⟩_ : ∀ x {Γ P Q}
      → ⟦ Q true-[ Γ , x ∶ (P true-[ Γ ]) ] ⟧
      → ⟦ P ⊃ Q true-[ Γ ] ⟧
    ⊃-member-eq⟨_⟩_ : ∀ x {Γ M N P Q}
      → ⟦ M == N ∈ Q [ Γ , x ∶ (P true-[ Γ ]) ] ⟧ 
      → ⟦ λ⟨ x ⟩ M == λ⟨ x ⟩ N ∈ P ⊃ Q [ Γ ] ⟧

    ⊃-elim : ∀ {Γ P Q}
      → ⟦ P ⊃ Q true-[ Γ ] ⟧
      → ⟦ P true-[ Γ ] ⟧
      → ⟦ Q true-[ Γ ] ⟧
    ⊃-elim-eq : ∀ {Γ M M′ N N′ P Q}
      → ⟦ M == M′ ∈ P ⊃ Q [ Γ ] ⟧
      → ⟦ N == N′ ∈ P [ Γ ] ⟧
      → ⟦ app M N == app M′ N′ ∈ Q [ Γ ] ⟧

    hyp⟨_⟩ : ∀ x {Γ Δ P}
         ⦃ _ : Ctxt.⟦ Γ ∋ x ∶ (P true-[ Δ ]) ⟧ ⦄
         ⦃ _ : Ctxt.⟦ Δ ≤ Γ ⟧ ⦄
      → ⟦ P true-[ Γ ] ⟧
    hyp-eq⟨_⟩ : ∀ x {Γ Δ P}
         ⦃ _ : Ctxt.⟦ Γ ∋ x ∶ (P true-[ Δ ]) ⟧ ⦄
         ⦃ _ : Ctxt.⟦ Δ ≤ Γ ⟧ ⦄
      → ⟦ var⟨ x ⟩ ∈ P [ Γ ] ⟧

    witness⟨_⟩_ : ∀ M {Γ P}
      → ⟦ M ∈ P [ Γ ] ⟧
      → ⟦ P true-[ Γ ] ⟧
  
  -- Every derivation in the logical theory has a corresponding
  -- derivation in the computational type theory.
  ⌜_⌝ : ∀ {Γ P} → L.⟦ P true-[ Γ ] ⟧ → ⟦ P true-[ Γ ] ⟧
  ⌜ L.⊤-intro ⌝ = ⊤-intro
  ⌜ L.⊥-elim D ⌝ = ⊥-elim ⌜ D ⌝
  ⌜ L.⊃-intro⟨ x ⟩ D ⌝ = ⊃-intro⟨ x ⟩ ⌜ D ⌝
  ⌜ L.⊃-elim D E ⌝ = ⊃-elim ⌜ D ⌝ ⌜ E ⌝
  ⌜ L.hyp⟨_⟩ x ⌝ = hyp⟨ x ⟩
 
  -- Every derivation in the computational type theory also may have a
  -- witness/realizer extracted from it.
  _° : ∀ {J} → ⟦ J ⟧ → term
  ⊤-intro ° = •
  (⊥-elim D) ° = abort D °
  (⊃-intro⟨ x ⟩ D) ° = λ⟨ x ⟩ D °
  ⊃-elim D E ° = app (D °) (E °)
  hyp⟨ x ⟩ ° = var⟨ x ⟩
  (witness⟨ M ⟩ D) ° = M
  ⊤-member-eq ° = •
  (⊥-elim-eq _) ° = •
  (⊃-member-eq⟨ x ⟩ _) ° = •
  ⊃-elim-eq _ _ ° = •
  hyp-eq⟨ x ⟩ ° = •
  (eq-sym _) ° = •
  eq-trans _ _ ° = •
 
  -- The computational realizers are well-typed in the type theory.
  coh : ∀ {Γ P} (D : L.⟦ P true-[ Γ ] ⟧) → ⟦ ⌜ D ⌝ ° ∈ P [ Γ ] ⟧
  coh L.⊤-intro = ⊤-member-eq
  coh (L.⊥-elim D) = ⊥-elim-eq coh D
  coh (L.⊃-intro⟨ x ⟩ D) = ⊃-member-eq⟨ x ⟩ coh D
  coh (L.⊃-elim D E) = ⊃-elim-eq (coh D) (coh E)
  coh (L.hyp⟨ x ⟩) = hyp-eq⟨ x ⟩

  theory : Theory.struct
  theory = record { term = term ; judgement = judgement ; ⟦_⟧ = ⟦_⟧ }
