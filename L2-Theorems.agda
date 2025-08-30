{-# OPTIONS --guardedness --safe --exact-split --copatterns #-}

open import Data.Nat hiding (_+_)
open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to maybeMap)
open import Data.Empty
open import Data.List using (List; []; _∷_) renaming (map to listMap)
open import Data.Sum
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function.Base using (case_of_)

open import L2
open import L2-Induction

data _⊨σ_∶_ : TypeEnv → σ → TypeEnv → Set where
    compatible : {Γ' : TypeEnv} → {s : σ} → {Γ : TypeEnv} → (∀ {x T Σ} → Γ(x) ≡ just T → (_⨾_⊢_∶_ Σ Γ' (lookup-var s x) T)) → Γ' ⊨σ s ∶ Γ

data _⊢ρ_∶_ : TypeEnv → ρ → TypeEnv → Set where
    compatible : {Γ' : TypeEnv} → {r : ρ} → {Γ : TypeEnv} → (∀ {x T} → Γ(x) ≡ just T → (Γ' (r x) ≡ just T)) → Γ' ⊢ρ r ∶ Γ

↑-has-type : ∀ {Γ T} → (Γ , T) ⊢ρ suc ∶ Γ
↑-has-type = compatible (λ {x} {T = T₁} z → z)

⇑ᵣ-equiv : ∀ {Γ Γ' r x T T'} → Γ' ⊢ρ r ∶ Γ → (Γ , T') x ≡ just T → (Γ' , T') ((⇑ᵣ r) x) ≡ just T
⇑ᵣ-equiv {Γ} {Γ'} {r} {zero} {T} {T'} p q = q
⇑ᵣ-equiv {Γ} {Γ'} {r} {suc x} {T} {T'} (compatible x₁) q = x₁ q

⇑ᵣ-has-type : ∀ {Γ Γ' T r} → Γ' ⊢ρ r ∶ Γ → (Γ' , T) ⊢ρ (⇑ᵣ r) ∶ (Γ , T)
⇑ᵣ-has-type p = compatible (⇑ᵣ-equiv p)

⇑-has-type : ∀ {Γ Γ' s T} → Γ' ⊨σ s ∶ Γ → (Γ' , T) ⊨σ ⇑ s ∶ (Γ , T)
⇑-has-type {Γ} {Γ'} {s} {T} p = compatible compatibility-proof where
    compatibility-proof : ∀ {x T' Σ } → (Γ , T) x ≡ just T' → Σ ⨾ (Γ' , T) ⊢ lookup-var (⇑ s) (x) ∶ T'
    compatibility-proof {zero} {T'} {Σ} x-type = var x-type
    compatibility-proof {suc x} {T'} {Σ} x-type = {!   !}

rename-compatibility : ∀ e {Σ Γ Γ' T T' r} →  Γ ⊢ρ r ∶ Γ' → Σ ⨾ Γ ⊢ e ∶ T → Σ ⨾ Γ' ⊢ (rename r e) ∶ T
rename-compatibility  =  {!   !}


LiftingSubHasType : ∀ {Γ Γ' s T} → Γ' ⊨σ s ∶ Γ → ((Γ' , T) ⊨σ (⇑ s) ∶ (Γ , T))
LiftingSubHasType {Γ} {Γ'} {s} {T} (compatible x) = compatible lift-proof where
    lift-proof : ∀ {y T' Σ} → (Γ , T)(y) ≡ just T' → (_⨾_⊢_∶_ Σ (Γ' , T) (lookup-var (⇑ s) y) T')
    lift-proof {zero} {T'} {Σ} l = var l
    lift-proof {suc z} {T'} {Σ} l = {!   !}

SubstitutionLemma : ∀ {Σ Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → (∀ {Γ' s} → Γ' ⊨σ s ∶ Γ → Σ ⨾ Γ' ⊢ subst s e ∶ T)
SubstitutionLemma {Σ} {_} {_} {_} derivation = ⊢-induction case derivation where
    P : TypeEnv → Expression → Type → Set
    P Γ e T = ∀ {Γ' s} → Γ' ⊨σ s ∶ Γ → Σ ⨾ Γ' ⊢ subst s e ∶ T
    case : ∀ {Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T
    case int ih compatibleSubst = int
    case bool ih compatibleSubst = bool
    case (op+ _ _) (op+ ih-e₁ ih-e₂) compatibleSubst = (op+ (ih-e₁ compatibleSubst) (ih-e₂ compatibleSubst))
    case (op≥ _ _) (op≥ ih-e₁ ih-e₂) compatibleSubst = op≥ (ih-e₁ compatibleSubst) (ih-e₂ compatibleSubst)
    case (if _ _ _) (if ih-e₁ ih-e₂ ih-e₃) compatibleSubst = if  (ih-e₁ compatibleSubst) (ih-e₂ compatibleSubst) (ih-e₃ compatibleSubst)
    case (assign _ _) (assign ℓ ih-e) compatibleSubst = assign ℓ (ih-e compatibleSubst)
    case (deref _) (deref ℓ) compatibleSubst = deref ℓ
    case skip ih compatibleSubst = skip
    case (seq _ _) (seq ih-e₁ ih-e₂) compatibleSubst = seq (ih-e₁ compatibleSubst) (ih-e₂ compatibleSubst)
    case (while _ _) (while ih-e₁ ih-e₂) compatibleSubst = while (ih-e₁ compatibleSubst) (ih-e₂ compatibleSubst)
    case (var x) ih (compatible s-x-well-typed) = s-x-well-typed x
    case (fn _) (fn ih-e) compatibleSubst = fn {!   !}
    case (app _ _)  (app ih-e₁ ih-e₂) compatibleSubst = app (ih-e₁ compatibleSubst) (ih-e₂ compatibleSubst)
    case (letval deriv deriv₁) ih compatibleSubst = {!   !}
    case (letrecfn deriv deriv₁) ih compatibleSubst = {!   !}
