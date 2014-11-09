{-# OPTIONS --type-in-type #-}

module theories-with-judgement where

auto : {P : Set} ⦃ M : P ⦄ → P
auto ⦃ M ⦄ = M

module Framework (name : Set) (_≠_ : name → name → Set) where
  record Theory : Set where
    field
      term : Set 
      judgement : Set
      ⟦_⟧ : judgement → Set
  
  module Contexts (T : Theory) where
    module T = Theory T

    data term : Set where
      · : term
      _,_∶_ : term → name → T.judgement → term
    infixl 9 _,_∶_

    data judgement : Set where
      _ctx : term → judgement
      _∉_ : name → term → judgement
      _∋_∶_ : term → name → T.judgement → judgement
      _≤_ : term → term → judgement
      
    infixl 8 _ctx
    infixr 8 _∉_
    infixr 8 _≤_
    
    data ⟦_⟧ : judgement → Set where
      ·-ctx : ⟦ · ctx ⟧
      Γ,x∶J-ctx : ∀ {Γ x J}
        → ⟦ Γ ctx ⟧
        → ⟦ x ∉ Γ ⟧
        → ⟦ Γ , x ∶ J ctx ⟧

      x∉· : ∀ {x}
        → ⟦ x ∉ · ⟧
      x∉Γ,y∶J : ∀ {Γ x y J}
        → x ≠ y
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

    
    thy : Theory
    thy = record { term = term ; judgement = judgement ; ⟦_⟧ = ⟦_⟧ }

  module Logic where

    data term : Set where
      ⊤ ⊥ : term
      _⊃_ : term → term → term

    thy : Theory
    module Ctx = Contexts thy
    open Ctx using (_ctx ; _∋_∶_ ; · ; _,_∶_ ; _≤_)

    data judgement : Set where
      _true-[_] : term → Contexts.term thy → judgement
    infixl 9 _true-[_]

    data ⟦_⟧ : judgement → Set
    thy = record { term = term ; judgement = judgement ; ⟦_⟧ = ⟦_⟧ }

    data ⟦_⟧ where
      ⊤-intro : ∀ {Γ}
        → Ctx.⟦ Γ ctx ⟧
        → ⟦ ⊤ true-[ Γ ] ⟧

      ⊥-elim : ∀ {Γ P}
        → Ctx.⟦ Γ ctx ⟧
        → ⟦ ⊥ true-[ Γ ] ⟧
        → ⟦ P true-[ Γ ] ⟧

      ⊃-intro⟨_⟩ : ∀ x {Γ P Q}
        → Ctx.⟦ Γ ctx ⟧
        → ⟦ Q true-[ Γ , x ∶ P true-[ Γ ] ] ⟧
        → ⟦ P ⊃ Q true-[ Γ ] ⟧

      ⊃-elim : ∀ {Γ P Q}
        → Ctx.⟦ Γ ctx ⟧
        → ⟦ P ⊃ Q true-[ Γ ] ⟧
        → ⟦ P true-[ Γ ] ⟧
        → ⟦ Q true-[ Γ ] ⟧

      hyp⟨_⟩ : ∀ x {Γ Δ P}
        → Ctx.⟦ Γ ctx ⟧
        → Ctx.⟦ Γ ∋ x ∶ (P true-[ Δ ]) ⟧
        → Ctx.⟦ Δ ≤ Γ ⟧
        → ⟦ P true-[ Γ ] ⟧

  -- A simple "computational type theory". Note that the
  -- presuppositions for context validity are different in CTT than in
  -- MLTT.
  module CTT where
    type : Set
    type = Logic.term

    data term : Set where
      • : term
      λ⟨_⟩_ : name → term → term
      abort_ : term → term
      var⟨_⟩ : name → term
      app : term → term → term

    thy : Theory
    module Ctx = Contexts Logic.thy
    open Ctx using (_ctx ; _∋_∶_ ; · ; _,_∶_ ; _≤_)
    open Logic using (⊤ ; ⊥; _⊃_ ; _true-[_])
 
    data judgement : Set where
      _==_∈_[_] : term → term → type → Ctx.term → judgement
      _true-[_] : type → Ctx.term → judgement

    infixl 8 _==_∈_[_]
    infixl 8 _∈_[_]

    _∈_[_] : term → type → Ctx.term → judgement
    M ∈ A [ Γ ] = M == M ∈ A [ Γ ]

    data ⟦_⟧ : judgement → Set
    
    thy = record { term = term ; judgement = judgement ; ⟦_⟧ = ⟦_⟧ }

    data ⟦_⟧ where
      ⊤-intro : ∀ {Γ}
        → ⟦ ⊤ true-[ Γ ] ⟧
      ⊤-member-eq : ∀ {Γ}
        → ⟦ • ∈ ⊤ [ Γ ] ⟧

      ⊥-elim : ∀ {Γ P}
        → ⟦ ⊥ true-[ Γ ] ⟧
        → ⟦ P true-[ Γ ] ⟧
      ⊥-elim-eq : ∀ {Γ M N P}
        → ⟦ M == N ∈ ⊥ [ Γ ] ⟧
        → ⟦ abort M == abort N ∈ P [ Γ ] ⟧

      ⊃-intro⟨_⟩ : ∀ x {Γ P Q}
        → ⟦ Q true-[ Γ , x ∶ P true-[ Γ ] ] ⟧
        → ⟦ P ⊃ Q true-[ Γ ] ⟧
      ⊃-member-eq⟨_⟩ : ∀ x {Γ M N P Q}
        → ⟦ M == N ∈ Q [ Γ , x ∶ P true-[ Γ ] ] ⟧ 
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
        → Ctx.⟦ Γ ∋ x ∶ (P true-[ Δ ]) ⟧
        → Ctx.⟦ Δ ≤ Γ ⟧
        → ⟦ P true-[ Γ ] ⟧
      hyp-eq⟨_⟩ : ∀ x {Γ Δ P}
        → Ctx.⟦ Γ ∋ x ∶ (P true-[ Δ ]) ⟧
        → Ctx.⟦ Δ ≤ Γ ⟧
        → ⟦ var⟨ x ⟩ ∈ P [ Γ ] ⟧

      witness⟨_⟩ : ∀ M {Γ P}
        → ⟦ M ∈ P [ Γ ] ⟧
        → ⟦ P true-[ Γ ] ⟧

    -- Every derivation in the logical theory has a corresponding derivation in the computational type theory.
    ⌜_⌝ : ∀ {Γ P} → Logic.⟦ P true-[ Γ ] ⟧ → ⟦ P true-[ Γ ] ⟧
    ⌜ Logic.⊤-intro _ ⌝ = ⊤-intro
    ⌜ Logic.⊥-elim _ D ⌝ = ⊥-elim ⌜ D ⌝
    ⌜ Logic.⊃-intro⟨ x ⟩ _ D ⌝ = ⊃-intro⟨ x ⟩ ⌜ D ⌝
    ⌜ Logic.⊃-elim _ D E ⌝ = ⊃-elim ⌜ D ⌝ ⌜ E ⌝
    ⌜ Logic.hyp⟨_⟩ x D E F ⌝ = hyp⟨ x ⟩ E F

    -- Every derivation in the computational type theory also may have a witness/realizer extracted from it.
    _° : ∀ {J} → ⟦ J ⟧ → term
    ⊤-intro ° = •
    ⊥-elim D ° = abort D °
    ⊃-intro⟨ x ⟩ D ° = λ⟨ x ⟩ D °
    ⊃-elim D E ° = app (D °) (E °)
    hyp⟨ x ⟩ _ _ ° = var⟨ x ⟩
    witness⟨ M ⟩ D ° = M
    ⊤-member-eq ° = •
    ⊥-elim-eq _ ° = •
    ⊃-member-eq⟨_⟩ _ _ ° = •
    ⊃-elim-eq _ _ ° = •
    hyp-eq⟨_⟩ _ _ _ ° = •

    -- The computational realizers are well-typed in the type theory.
    coh : ∀ {Γ P} (D : Logic.⟦ P true-[ Γ ] ⟧) → ⟦ ⌜ D ⌝ ° ∈ P [ Γ ] ⟧
    coh (Logic.⊤-intro _) = ⊤-member-eq
    coh (Logic.⊥-elim _ D) = ⊥-elim-eq (coh D)
    coh (Logic.⊃-intro⟨ x ⟩ _ D) = ⊃-member-eq⟨ x ⟩ (coh D)
    coh (Logic.⊃-elim _ D E) = ⊃-elim-eq (coh D) (coh E)
    coh (Logic.hyp⟨ x ⟩ _ D E) = hyp-eq⟨ x ⟩ D E

    module example {x : name} where
      test : ⟦ λ⟨ x ⟩ abort var⟨ x ⟩ ∈ ⊥ ⊃ ⊤ [ · ] ⟧
      test = ⊃-member-eq⟨ x ⟩ (⊥-elim-eq (hyp-eq⟨ x ⟩ auto auto))

      test₂ : ⟦ ⊥ ⊃ ⊤ true-[ · ] ⟧
      test₂ = ⊃-intro⟨ x ⟩ (⊥-elim (hyp⟨ x ⟩ auto auto))
