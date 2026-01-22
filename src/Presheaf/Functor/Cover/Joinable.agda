{-# OPTIONS --safe #-}

open import Frame.IFrame
import Frame.CFrame as CF

module Presheaf.Functor.Cover.Joinable
  {W    : Set}
  {_⊆_  : (w w' : W) → Set}
  (IF   : IFrame W _⊆_)
  (let open CF IF)
  (K   : W → Set)
  (_∈_ : (v : W) {w : W} → K w → Set)
  (let open Core K _∈_ renaming (NFam to KFam))
  (CF  : CFrame)
  (JCF : Joinable CF)
  where

open IFrame IF
open CFrame CF
open Joinable JCF

open import Presheaf.Base IF
open import Presheaf.CartesianClosure IF
open import Presheaf.Functor.Cover.Base IF CF

open import PUtil
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; cong to ≡-cong
           ; cong₂ to ≡-cong₂ ; subst to ≡-subst ; subst₂ to ≡-subst₂)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Data.Product
  using (∃; Σ; _×_; _,_; -,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import PEUtil using (subst-application′′)
open import HEUtil

private
  variable
    w w' w'' u u' v v' : W
    𝒫 𝒫' 𝒬 𝒬' ℛ ℛ' ℛ'' : Psh

module _ (𝒫 : Psh) where

  -- "element tree"
  ElTree[_] : {α : K w} → (α[_] : KFam α) → Set
  ElTree[_] = Tree[ 𝒫 ₀_ ]


  -- extensional equivalence for element trees
  ElTree[_]≋ : {α : K w} {α[_] α[_]' : KFam α}
    → (f : ElTree[_] α[_]) (f' : ElTree[_] α[_]') → Set
  ElTree[_]≋ {α = α} f f' = {u u' : W} {p : u ∈ α} {p' : u' ∈ α}
    → u ≡ u' → p ≅ p' → ElFam[ 𝒫 ]≋ (f {u} p) (f' {u'} p')

  -- congruence for element trees
  ≋[_]-cong-ElTree : {α : K w} {α[_] : KFam α}
    → (f : ElTree[_] α[_])
    → {u u' : W} (u≡u' : u ≡ u')
    → {p : u ∈ α} {p' : u' ∈ α} (p≅p' : p ≅ p')
    → {v : W} {q : v ∈ α[ p ]} {q' : v ∈ α[ p' ]} (q≅q' : q ≅ q')
    → f {u} p q ≋[ 𝒫 ] f {u'} p' q'
  ≋[_]-cong-ElTree f ≡-refl ≅-refl ≅-refl = ≋[ 𝒫 ]-refl

  -- congruence for a special case of GTrees (TODO: generalize)
  ≋[_]-cong-GTree : {α : K w} {α[_] : KFam α} {α[_][_] : Tree[ K ] α[_]}
    → (f : GTree[ KFam ∘ α[_] , ElTree[_] ] α[_][_])
    → {x x' : W} (x≡x' : x ≡ x')
    → {p : x ∈ α} {p' : x' ∈ α} (p≅p' : p ≅ p')
    → {y y' : W} (y≡y' : y ≡ y')
    → {q : y ∈ α[ p ]} {q' : y' ∈ α[ p' ]} (q≅q' : q ≅ q')
    → {z : W} {r : z ∈ α[ p ][ q ]} {r' : z ∈ α[ p' ][ q' ]} (r≅r' : r ≅ r')
    → f {x} p {y} q r ≋[ 𝒫 ] f {x'} p' {y'} q' r'
  ≋[_]-cong-GTree f ≡-refl ≅-refl ≡-refl ≅-refl ≅-refl = ≋[ 𝒫 ]-refl

  -- weakening/refining element trees
  wkElTree[_] : {α : K w} {α[_] : KFam α} {α' : K w'}
    → (is : α ≼ α')
    → ElTree[_]  α[_]
    → ElTree[_] (wkNFam is α[_])
  wkElTree[_] {α = α} {α[_]} α≼α' tr {u'} u'∈α' {v'} v'∈α[u'] = let
      (u , u∈α , u⊆u') = α≼α' u'∈α'
      (α'[p] , α[u]≼α'[u']) = refine u⊆u' α[ u∈α ]
      (v , v∈α[u] , v⊆v') = α[u]≼α'[u'] v'∈α[u']
      in wk[ 𝒫 ] v⊆v' (tr u∈α v∈α[u])

joinElFam[_] : (𝒫 : Psh) → {α : K w} (α[_] : KFam α) → ElTree[ 𝒫 ] α[_] → ElFam[ 𝒫 ] (⨆ α[_])
joinElFam[ 𝒫 ] = joinFam[ 𝒫 ₀_ ]

joinElFam[_]-assoc : (𝒫 : Psh) {α : K w} {α[_] : KFam α} {α[_][_] : Tree[ K ] α[_]}
  → (tr : ForAll∈ α (ElTree[ 𝒫 ] ∘ α[_][_]))
  → ElFam[ 𝒫 ]≋
      (joinElFam[ 𝒫 ] (joinNFamᵢ α[_] α[_][_])
        (λ x∈α → uncurry∈ (λ y∈α[x] → tr x∈α y∈α[x]) ∘ ⨆-bwd-member α[ x∈α ][_]))
      (joinElFam[ 𝒫 ] (joinNFamₑ α[_] α[_][_])
        (uncurry∈ (λ x∈α → tr x∈α) ∘ ⨆-bwd-member α[_]))
joinElFam[ 𝒫 ]-assoc {α} {α[_]} {α[_][_]} tr {z} {z∈ji} {z∈je} r≅r' = let
  -- LHS
  (x , x∈α , z∈⨆α[x][-]) = ⨆-bwd-member (joinNFamᵢ α[_] α[_][_]) z∈ji
  (y , y∈α[x] , z∈α[x][y]) = ⨆-bwd-member α[ x∈α ][_] z∈⨆α[x][-]
  -- RHS
  (y' , y'∈⨆α[-] , z∈α[x'][y']) = ⨆-bwd-member (joinNFamₑ α[_] α[_][_]) z∈je
  (x' , x'∈α , y'∈α[x']) = ⨆-bwd-member α[_] y'∈⨆α[-]
  (x≡x' , x∈α≅x'∈α , y≡y' , y∈α[x]≅y'∈α[x'] , z∈α[x][y]≅z∈α[x'][y']) = ⨆-bwd-member-resp-assoc r≅r'
  open EqReasoning ≋[ 𝒫 ]-setoid
  in begin
    joinElFam[ 𝒫 ]
      (joinNFamᵢ α[_] α[_][_])
      (λ x∈α → uncurry∈ (λ y∈α[x] → tr x∈α y∈α[x]) ∘ ⨆-bwd-member (α[_][_] x∈α)) z∈ji
      ≡⟨⟩
    tr {x} x∈α {y} y∈α[x] {z} z∈α[x][y]
      ≈⟨ ≋[ 𝒫 ]-cong-GTree tr x≡x' x∈α≅x'∈α y≡y' y∈α[x]≅y'∈α[x'] z∈α[x][y]≅z∈α[x'][y'] ⟩
    tr {x'} x'∈α {y'} y'∈α[x'] {z} z∈α[x'][y']
      ≡⟨⟩
    joinElFam[ 𝒫 ]
      (joinNFamₑ α[_] α[_][_])
      (uncurry∈ (λ x∈α → tr x∈α) ∘ ⨆-bwd-member α[_]) z∈je
      ∎

join[_] : ∀ 𝒫 → 𝒞 𝒞 𝒫 →̇ 𝒞 𝒫
join[ 𝒫 ] = record
  { fun     = join-fun
  ; pres-≋  = join-fun-pres-≋
  ; natural = join-fun-natural
  }
  where

  joinElFam : {α : K w} (α[_] : KFam α) → ElTree[ 𝒫 ] α[_] → ElFam[ 𝒫 ] (⨆ α[_])
  joinElFam = joinElFam[ 𝒫 ]

  opaque



    joinElFam-pres-≋ : {α : K w} {α[_] α[_]' : KFam α}
      → {tr  : ElTree[ 𝒫 ] α[_]} {tr' : ElTree[ 𝒫 ] α[_]'}
      → ForAllW≅ α[_] α[_]' → ElTree[ 𝒫 ]≋ tr tr'
      → ElFam[ 𝒫 ]≋ (joinElFam α[_] tr) (joinElFam α[_]' tr')
    joinElFam-pres-≋  α[-]≋α'[-] tr≋tr' r≅r' =
      let (u≡u' , p≅p' , q≅q') = ⨆-bwd-member-pres-≋ α[-]≋α'[-] r≅r'
      in tr≋tr' u≡u' p≅p' q≅q'

    joinElFam-natural : {α : K w} {α' : K w'}
      → {α[_] : KFam α} {tr : ElTree[ 𝒫 ] α[_]}
      → (α≼α' : α ≼ α')
      → ElFam[ 𝒫 ]≋
          (wkElFam[ 𝒫 ] (⨆-pres-≼ α≼α' α[_]) (joinElFam α[_] tr))
          (joinElFam (wkNFam α≼α' α[_]) (wkElTree[ 𝒫 ] α≼α' tr))
    joinElFam-natural {α = α} {α'} {α[_] = α[_]} {tr} α≼α' {v'} {v'∈⨆α'[-]} ≅-refl = let
      α'[_]                   = wkNFam α≼α' α[_]
      (v , v∈⨆α[-] , v⊆v')    = ⨆-pres-≼ α≼α' α[_] v'∈⨆α'[-] -- uses ⨆-fwd-member
      -- LHS stuff
      (u' , u'∈α' , v'∈α'[u']) = ⨆-bwd-member α'[_] v'∈⨆α'[-]
      (u , u∈α , u⊆u')         = α≼α' u'∈α'
      (α'[u'] , α[u]≼α'[u'])   = refine u⊆u' α[ u∈α ]
      (v , v∈α[u] , v⊆v')      = α[u]≼α'[u'] v'∈α'[u']
      -- RHS stuff
      (zᵤ , zᵤ∈α , v∈α[zᵤ])  = ⨆-bwd-member α[_] v∈⨆α[-]
      -- Equivalence
      (zᵤ≡u , zᵤ∈α≅u∈α , v∈α[zᵤ]≅v∈α[u]) = ⨆-fwd-bwd-id (u , u∈α , v∈α[u])
      open EqReasoning ≋[ 𝒫 ]-setoid in
      begin
        wkElFam[ 𝒫 ] (⨆-pres-≼ α≼α' α[_]) (joinElFam α[_] tr) v'∈⨆α'[-]
          ≡⟨⟩ -- expand wkElFam
        wk[ 𝒫 ] v⊆v' (joinElFam α[_] tr v∈⨆α[-])
          ≡⟨⟩ -- expand joinElFam
        wk[ 𝒫 ] v⊆v' (tr {zᵤ} zᵤ∈α v∈α[zᵤ])
          ≈⟨ wk[ 𝒫 ]-pres-≋ v⊆v' (≋[ 𝒫 ]-cong-ElTree tr zᵤ≡u zᵤ∈α≅u∈α v∈α[zᵤ]≅v∈α[u]) ⟩
        wk[ 𝒫 ] v⊆v' (tr {u} u∈α v∈α[u])
          ≡⟨⟩ -- contract wkElTree
        wkElTree[ 𝒫 ] α≼α' tr u'∈α' v'∈α'[u']
          ≡⟨⟩ -- contract joinElFam
        joinElFam α'[_] (wkElTree[ 𝒫 ] α≼α' tr) v'∈⨆α'[-]
          ∎

  join-fun : 𝒞-Fam (𝒞 𝒫) w → 𝒞-Fam 𝒫 w
  join-fun (elem α fam) = elem (⨆ (cov ∘ fam)) (joinElFam (cov ∘ fam) (elems ∘ fam))

  opaque
    join-fun-pres-≋ : {cx cx' : 𝒞-Fam (𝒞 𝒫) w}
      → cx 𝒞-≋[ 𝒞 𝒫 ] cx' → join-fun cx 𝒞-≋[ 𝒫 ] join-fun cx'
    join-fun-pres-≋ {cx = elem α fam} {cx' = elem α' fam'} (proof ≡-refl fam≋fam')
      = proof
          (⨆-pres-≋ (≡-refl , cov≋ ∘ fam≋fam'))
          (joinElFam-pres-≋ (≡-refl , cov≋ ∘ fam≋fam') (λ { ≡-refl → elems≋ ∘ fam≋fam'}))

    join-fun-natural : (i : w ⊆ w') (p : (𝒞 (𝒞 𝒫)) ₀ w) →
      wk[ 𝒞 𝒫 ] i (join-fun p) ≋[ 𝒞 𝒫 ] join-fun (wk[ 𝒞 (𝒞 𝒫) ] i p)
    join-fun-natural i (elem α fam) = let
      α[_] : KFam α
      α[_] = cov ∘ fam
      tr : {u : W} (p : u ∈ α) → ElFam[ 𝒫 ] α[ p ]
      tr = elems ∘ fam
      (rjα≡jrα , is≋is') = refine-coh-joinN i α α[_]
      in proof rjα≡jrα λ {v} {p} {p'} p≅p' →
        let open EqReasoning ≋[ 𝒫 ]-setoid
        in begin
          wkElFam[ 𝒫 ] (refine i $≼ (⨆ α[_])) (joinElFam α[_] tr) p
            ≈⟨ wkElFam-pres-≋-left {𝒫  = 𝒫} is≋is' (joinElFam α[_] tr) p≅p' ⟩
          wkElFam[ 𝒫 ] (⨆-pres-≼ (refine i $≼ α) α[_]) (joinElFam α[_] tr) p'
            ≈⟨ joinElFam-natural {tr = tr} (refine i $≼ α) ≅-refl ⟩
          joinElFam (wkNFam (refine i $≼ α) α[_]) (wkElTree[ 𝒫 ] (refine i $≼ α) tr) p'
            ∎

opaque
  unfolding 𝒞-map_ _≈̇_

  -- join is a natural transformation from the composition of functors 𝒞 ∘' 𝒞 to 𝒞
  join-natural : (t :  𝒫 →̇  𝒬) → join[ 𝒬 ] ∘' (𝒞-map (𝒞-map t)) ≈̇ (𝒞-map t) ∘' join[ 𝒫 ]
  join-natural {𝒫} {𝒬} t = λ _p → proof ≡-refl λ { ≅-refl → ≋[ 𝒬 ]-refl }

  open import Presheaf.Functor.Cover.Base as B using ()

  join-assoc : join[ 𝒫 ] ∘' (𝒞-map join[ 𝒫 ]) ≈̇ join[ 𝒫 ] ∘' join[ 𝒞 𝒫 ]
  join-assoc {𝒫} (elem α fam) = proof joinN-assoc (joinElFam[ 𝒫 ]-assoc λ v∈α → elems ∘ elems (fam v∈α))

join = λ {𝒫} → join[ 𝒫 ]
