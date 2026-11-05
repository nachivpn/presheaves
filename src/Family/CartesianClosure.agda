{-# OPTIONS --safe --without-K #-}

open import Frame.IFrame

module Family.CartesianClosure (W : Set) where

open import Family.Base W

open import Function using (id)

open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import Data.Unit using (⊤; tt)
open import Data.Unit.Properties using () renaming (⊤-irrelevant to ⊤-eta)

open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality.Properties using () renaming (isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Algebra.Lib

private
  variable
    w v              : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' : Psh
    s s' t t' u u'   : 𝒫 →̇ 𝒬

--
-- Cartesian products
--

Unit' : Psh
Unit' = record
  { Fam           = λ _w → ⊤
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _w → ≡-equiv
  }

⊤' = Unit'
1' = ⊤'

unit' : ℛ →̇ Unit'
unit' = record
  { fun     = λ _r → tt
  ; pres-≋  = λ {w} _p≋p' → ≋[ Unit' ]-refl {w}
  }

unit'[_] = λ ℛ → unit' {ℛ}

opaque
  Unit'-eta : t ≈̇ unit'
  Unit'-eta {ℛ} {t} = proof-≈̇ (λ r → ⊤-eta (t .apply r) (unit'[ ℛ ] .apply r))

⊤'-eta = Unit'-eta

module _ (𝒫 𝒬 : Psh) where
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  record Fam (w : W) : Set where
    constructor elem
    field
      pair : P w × Q w

  record _≋_ {w : W} (x y : Fam w) : Set where
    constructor proof
    field
      proof : let elem (p , q) = x; elem (p' , q') = y in p ≋[ 𝒫 ] p' × q ≋[ 𝒬 ] q'

  private
    ≋-equiv : ∀ (w : W) → IsEquivalence (_≋_ {w})
    ≋-equiv _w = record
      { refl  = proof (≋[ 𝒫 ]-refl , ≋[ 𝒬 ]-refl)
      ; sym   = λ (proof (p≋p' , q≋q')) → proof (≋[ 𝒫 ]-sym p≋p' , ≋[ 𝒬 ]-sym q≋q')
      ; trans = λ (proof (p≋p' , q≋q')) (proof (p'≋p'' , q'≋q'')) → proof (≋[ 𝒫 ]-trans p≋p' p'≋p'' , ≋[ 𝒬 ]-trans q≋q' q'≋q'')
      }

  _×'_ : Psh
  _×'_ = record
    { Fam           = Fam
    ; _≋_           = _≋_
    ; ≋-equiv       = ≋-equiv
    }

module _ {𝒫 𝒬 : Psh} where
  π₁' : 𝒫 ×' 𝒬 →̇ 𝒫
  π₁' = record
    { fun     = λ x → let elem (p , _q) = x in p
    ; pres-≋  = λ x≋y → let proof (p≋p' , _q≋q') = x≋y in p≋p'
    }

  π₂' : 𝒫 ×' 𝒬 →̇ 𝒬
  π₂' = record
    { fun     = λ x → let elem (_p , q) = x in q
    ; pres-≋  = λ x≋y → let proof (_p≋p' , q≋q') = x≋y in q≋q'
    }

  fst' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒫
  fst' = π₁' ∘'_

  snd' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒬
  snd' = π₂' ∘'_

  pair' : (t : ℛ →̇ 𝒫) → (u : ℛ →̇ 𝒬) → ℛ →̇ 𝒫 ×' 𝒬
  pair' t u = record
    { fun     = λ r → elem (t .apply r , u .apply r)
    ; pres-≋  = λ r≋r' → proof (t .apply-≋ r≋r' , u .apply-≋ r≋r')
    }

  ⟨_,_⟩' = pair'

  opaque
    pair'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → pair' t u ≈̇ pair' t' u'
    pair'-pres-≈̇ t≈̇t' u≈̇u' = proof-≈̇ (λ r → proof (apply-≈̇ t≈̇t' r , apply-≈̇ u≈̇u' r))

    pair'-nat : ∀ (t : ℛ →̇ 𝒫) (u : ℛ →̇ 𝒬) (s : ℛ' →̇ ℛ) → pair' t u ∘' s ≈̇ pair' (t ∘' s) (u ∘' s)
    pair'-nat _t _u _s = proof-≈̇ (λ p → ≋[ 𝒫 ×' 𝒬 ]-refl)

    ×'-beta-left : ∀ {t : ℛ →̇ 𝒫} (u : ℛ →̇ 𝒬) → fst' (pair' t u) ≈̇ t
    ×'-beta-left {_t} _u = proof-≈̇ (λ _r → ≋[ 𝒫 ]-refl)

    ×'-beta-right : ∀ (t : ℛ →̇ 𝒫) {u : ℛ →̇ 𝒬} → snd' (pair' t u) ≈̇ u
    ×'-beta-right t {_u} = proof-≈̇ (λ _r → ≋[ 𝒬 ]-refl)

    ×'-eta : t ≈̇ pair' (fst' t) (snd' t)
    ×'-eta = proof-≈̇ (λ _r → ≋[ 𝒫 ×' 𝒬 ]-refl)

  opaque
    pair'-pres-≈̇-left : t ≈̇ t' → pair' t u ≈̇ pair' t' u
    pair'-pres-≈̇-left {u = u} t≈̇t' = pair'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    pair'-pres-≈̇-right : u ≈̇ u' → pair' t u ≈̇ pair' t u'
    pair'-pres-≈̇-right {t = t} u≈̇u' = pair'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'


π₁'[_] = λ {𝒫} 𝒬 → π₁' {𝒫} {𝒬}

π₁'[_][_] = λ 𝒫 𝒬 → π₁' {𝒫} {𝒬}

π₂'[_] = λ 𝒫 {𝒬} → π₂' {𝒫} {𝒬}

π₂'[_][_] = λ 𝒫 𝒬 → π₂' {𝒫} {𝒬}

_×'-map_ : (t : 𝒫 →̇ 𝒫') → (u : 𝒬 →̇ 𝒬') → 𝒫 ×' 𝒬 →̇ 𝒫' ×' 𝒬'
_×'-map_ {𝒫 = 𝒫} {𝒬 = 𝒬} t u = pair' (t ∘' π₁'[ 𝒬 ]) (u ∘' π₂'[ 𝒫 ])

assoc' : (𝒫 ×' 𝒬) ×' ℛ →̇ 𝒫 ×' (𝒬 ×' ℛ)
assoc' = ⟨ π₁' ∘' π₁' , ⟨ π₂' ∘' π₁' , π₂' ⟩' ⟩'

opaque
  ×'-map-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → t ×'-map u ≈̇ t' ×'-map u'
  ×'-map-pres-≈̇ t≈̇t' u≈̇u' = proof-≈̇ (λ x → let elem (p , q) = x in proof (apply-≈̇ t≈̇t' p , apply-≈̇ u≈̇u' q))

  ×'-map-pres-id : ∀ {𝒫 𝒬 : Psh} → id'[ 𝒫 ] ×'-map id'[ 𝒬 ] ≈̇ id'[ 𝒫 ×' 𝒬 ]
  ×'-map-pres-id {𝒫} {𝒬} = proof-≈̇ (λ _x → ≋[ 𝒫 ×' 𝒬 ]-refl)

opaque
  ×'-map-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : 𝒬 →̇ 𝒬') → t ×'-map u ≈̇ t' ×'-map u
  ×'-map-pres-≈̇-left t≈̇t' u = ×'-map-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

  ×'-map-pres-≈̇-right : ∀ (t : 𝒫 →̇ 𝒫') (_ : u ≈̇ u') → t ×'-map u ≈̇ t ×'-map u'
  ×'-map-pres-≈̇-right t u≈̇u' = ×'-map-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

--
-- Exponentials
--

module _ (𝒫 𝒬 : Psh) where
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  record →'-Fam (w : W) : Set where
    constructor elem
    field
      fun     : P w → Q w
      pres-≋  : {p p' : P w} → (p≋p' : p ≋[ 𝒫 ] p') → fun p ≋[ 𝒬 ] fun p'

  open →'-Fam renaming (fun to apply; pres-≋ to apply-≋) public

  record _→'-≋_ {w : W} (f g : →'-Fam w) : Set where
    constructor proof
    field
      pw : ∀ (p : P w) → f .apply p ≋[ 𝒬 ] g .apply p

  open _→'-≋_ using (pw) public

  private
    →'-≋-equiv : ∀ (_w : W) → IsEquivalence (_→'-≋_ {_w})
    →'-≋-equiv _w = record
      { refl  = proof (λ _p → ≋[ 𝒬 ]-refl)
      ; sym   = λ {f} {g} f≋g → proof (λ p → ≋[ 𝒬 ]-sym (f≋g .pw p))
      ; trans = λ {f} {g} {h} f≋g g≋h → proof (λ p → ≋[ 𝒬 ]-trans (f≋g .pw p) (g≋h .pw p))
      }

  _→'_ : Psh
  _→'_ = record
    { Fam           = →'-Fam
    ; _≋_           = _→'-≋_
    ; ≋-equiv       = →'-≋-equiv
    }

module _ {𝒫 𝒬 : Psh} where
  private
    →'-≋-apply-sq : ∀ {f g : 𝒫 →' 𝒬 ₀ w} (_f≋g : f ≋[ 𝒫 →' 𝒬 ] g) {p p' : 𝒫 ₀ w} → (_p≋p' : p ≋[ 𝒫 ] p') → f .apply p ≋[ 𝒬 ] g .apply p'
    →'-≋-apply-sq {_w} {f} {g} f≋g {p} {p'} p≋p' = let open EqReasoning ≋[ 𝒬 ]-setoid in begin
      f .apply p   ≈⟨ f .apply-≋ p≋p' ⟩
      f .apply p'  ≈⟨ f≋g .pw p' ⟩
      g .apply p'  ∎

  app' : (t : ℛ →̇ 𝒫 →' 𝒬) → (u : ℛ →̇ 𝒫) → ℛ →̇ 𝒬
  app' {ℛ} t u = record
    { fun     = λ r → t .apply r .apply (u .apply r)
    ; pres-≋  = λ r≋r' → →'-≋-apply-sq (t .apply-≋ r≋r') (u .apply-≋ r≋r')
    }

  opaque
    app'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → app' t u ≈̇ app' t' u'
    app'-pres-≈̇ t≈̇t' u≈̇u' = proof-≈̇ (λ r → →'-≋-apply-sq (apply-≈̇ t≈̇t' r) (apply-≈̇ u≈̇u' r))

    app'-nat : ∀ (t : ℛ →̇ 𝒫 →' 𝒬) (u : ℛ →̇ 𝒫) (s : ℛ' →̇ ℛ) → app' t u ∘' s ≈̇ app' (t ∘' s) (u ∘' s)
    app'-nat _t _u _s = proof-≈̇ (λ _r' → ≋[ 𝒬 ]-refl)

    app'-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : ℛ →̇ 𝒫) → app' t u ≈̇ app' t' u
    app'-pres-≈̇-left t≈̇t' u = app'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    app'-pres-≈̇-right : ∀ (t : ℛ →̇ 𝒫 →' 𝒬) (_ : u ≈̇ u') → app' t u ≈̇ app' t u'
    app'-pres-≈̇-right t u≈̇u' = app'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

lam' : (t : ℛ ×' 𝒫 →̇ 𝒬) → ℛ →̇ 𝒫 →' 𝒬
lam' {ℛ} {𝒫} {𝒬} t = record
  { fun     = λ r → record
                { fun     = λ p → t .apply (elem (r , p))
                ; pres-≋  = λ p≋p' → t .apply-≋ (proof (≋[ ℛ ]-refl , p≋p'))
                }
  ; pres-≋  = λ r≋r' → proof λ p → t .apply-≋ (proof (r≋r' , ≋[ 𝒫 ]-refl))
  }

opaque
  lam'-pres-≈̇ : t ≈̇ t' → lam' t ≈̇ lam' t'
  lam'-pres-≈̇ {_𝒬} {ℛ} {𝒫} t≈̇t' = proof-≈̇ (λ r → proof (λ p → apply-≈̇ t≈̇t' (elem (r , p))))

  →'-beta : ∀ (t : ℛ ×' 𝒫 →̇ 𝒬) (u : ℛ →̇ 𝒫) → app' (lam' t) u ≈̇ t [ pair' id' u ]'
  →'-beta {ℛ} {𝒫} t u = proof-≈̇ λ r → t .apply-≋ (proof (≋[ ℛ ]-refl , ≋[ 𝒫 ]-refl))

  →'-eta : ∀ (t : ℛ →̇ 𝒫 →' 𝒬) → t ≈̇ lam' {𝒬 = 𝒬} (app' (t [ π₁'[ 𝒫 ] ]') π₂'[ ℛ ])
  →'-eta {ℛ} {𝒫} {𝒬} t = proof-≈̇ λ r → proof (λ p → ≋[ 𝒬 ]-refl)



𝒲̂-cartesian : Cartesian 𝒲̂
𝒲̂-cartesian = record
  { terminal = record
    { ⊤             = ⊤'
    ; ⊤-is-terminal = record { ! = unit' ; !-unique = λ _ → ≈̇-sym (⊤'-eta) }
    }
  ; products =  record
    { product = λ {𝒫} {𝒬} → record
      { A×B      = 𝒫 ×' 𝒬
      ; π₁       = π₁'
      ; π₂       = π₂'
      ; ⟨_,_⟩    = ⟨_,_⟩'
      ; project₁ = λ {_} {h} {i} → ×'-beta-left i
      ; project₂ = λ {_} {h} {i} → ×'-beta-right h
      ; unique   = λ p q → ≈̇-sym (≈̇-trans ×'-eta (pair'-pres-≈̇ p q))
      }
    }
  }

𝒲̂-closed : CartesianClosed 𝒲̂
𝒲̂-closed = record
  { cartesian = 𝒲̂-cartesian
  ; exp = λ {𝒫} {𝒬} → record
    { B^A      = 𝒫 →' 𝒬
    ; eval     = app' π₁' π₂'
    ; λg       = lam'
    ; β        = →'-beta′
    ; λ-unique = →'-eta′
    }
  }
  where
    eval' : (𝒫 →' 𝒬) ×' 𝒫 →̇ 𝒬
    eval' = app' π₁' π₂'

    -- Note: The laws below could be derived from →'-beta and →'-eta
    -- but the proofs seem a bit lengthy and require additional lemmas.
    -- I'll avoid it as it might also slow down typechecking.

    →'-beta′ : {t : ℛ ×' 𝒫 →̇ 𝒬} → eval' ∘' (lam' t ×'-map id') ≈̇ t
    →'-beta′ {𝒬 = 𝒬} = proof-≈̇ (λ { (elem (p , q)) → ≋[ 𝒬 ]-refl })

    →'-eta′ : {g : ℛ ×' 𝒫 →̇ 𝒬} {h : ℛ →̇ (𝒫 →' 𝒬)} → eval' ∘' (h ×'-map id') ≈̇ g → h ≈̇ lam' g
    →'-eta′ eq = proof-≈̇ (λ p → proof λ q → apply-≈̇ eq (elem (p , q)))
