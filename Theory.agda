module Theory {i} where

open import Agda.Primitive

record struct : Set (lsuc i) where
  field
    term : Set i
    judgement : Set i
    ⟦_⟧ : judgement → Set i
