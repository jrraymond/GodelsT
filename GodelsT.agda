{- Justin Raymond
  GodelsT with lazy successor and call-by-name application.
  Proof of preservation and progress.
-}
module GodelsT where
  
  data Either (A B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B

  data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) → B a → Σ A B

  syntax Σ A (\ x  -> B) = Σ[ x ∈ A ] B

  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A
  
  data Typ : Set where
    nat : Typ
    arr : (τ₁ : Typ) → (τ₂ : Typ) → Typ

  {- A context is a list of types -}
  Ctx = List Typ

  {- deBruijn indices, there are two constructors. -}
  data _∈_ {τ : Set} : τ → List τ → Set where
    i0 : {x : τ} {xs : List τ} → x ∈ (x :: xs)
    iS : {x y : τ} {xs : List τ} → y ∈ xs → y ∈ (x :: xs)

  {- Static semantics. Γ ⊢ k means k is derivable from the rules Γ -}
  data _⊢_ (Γ : Ctx) : Typ → Set where
    z : Γ ⊢ nat
    var : ∀{τ} → (x : τ ∈ Γ) → Γ ⊢ τ
    s : (Γ ⊢ nat) → Γ ⊢ nat
    rec : ∀{τ} → (Γ ⊢ τ) → ((nat :: (τ :: Γ)) ⊢ τ) → (Γ ⊢ nat) → Γ ⊢ τ
    lam : ∀{τ ρ} → ((ρ :: Γ) ⊢ τ) → Γ ⊢ (arr ρ τ)
    ap : ∀{τ₂ τ} → (Γ ⊢ arr τ₂ τ) → (Γ ⊢ τ₂) → Γ ⊢ τ

  {- Inductive family parameterized by τ represented the values in Godels T-}
  data Value : ∀ {τ} → ([] ⊢ τ) → Set where
    z-value : Value z
    s-value : ∀{e} → Value (s e)
    lam-value : ∀{ρ τ} (e : (ρ :: []) ⊢ τ)  → Value (lam e)

  {- Proof of renaming and required lemmas. -}
  rename-ctx : Ctx → Ctx → Set
  rename-ctx Γ₁ Γ₂ = ∀ {τ} → τ ∈ Γ₁ → τ ∈ Γ₂
  rctx-cons : ∀{Γ₁ Γ₂ τ} → rename-ctx Γ₁ Γ₂ → rename-ctx (τ :: Γ₁) (τ :: Γ₂)
  rctx-cons x i0 = i0
  rctx-cons x (iS y) = iS (x y) 

  rename : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊢ τ → rename-ctx Γ₁ Γ₂ → Γ₂ ⊢ τ
  rename z r = z
  rename (var x) r = var (r x)
  rename (s e) r = s (rename e r)
  rename (rec e₀ e₁ e) r = rec (rename e₀ r) (rename e₁ (rctx-cons (rctx-cons r))) (rename e r)
  rename (lam e) r = lam (rename e (rctx-cons r))
  rename (ap e₁ e₂) r = ap (rename e₁ r) (rename e₂ r) 

  {- Lemma 4.4 substitution: If Γ, x : τ ⊢ e' : τ' and Γ ⊢ e : τ, then Γ ⊢ [e/x]e' : τ' -}
  {- Some lemmas we need to prove 4.4: -}
  swap-ctx : Ctx → Ctx → Set
  swap-ctx Γ₁ Γ₂ = ∀{τ} → τ ∈ Γ₂ → Γ₁ ⊢ τ
  lemma : ∀{Γ₁ Γ₂ τ} → swap-ctx Γ₁ Γ₂ → swap-ctx (τ :: Γ₁) (τ :: Γ₂)                                              
  lemma c₁ i0 =  (var i0) 
  lemma c₁ (iS i0) = rename (c₁ i0) iS
  lemma c₁ (iS (iS c₂)) = rename (c₁ (iS c₂)) iS
  lemma1 : ∀ {Γ τ} → Γ ⊢ τ → swap-ctx Γ (τ :: Γ)
  lemma1 x i0 = x
  lemma1 x (iS v) = var v
  lemma2 : ∀ {Γ τ τ'} → Γ ⊢ τ → Γ ⊢ τ' → swap-ctx Γ (τ :: (τ' :: Γ))
  lemma2 x y i0 = x
  lemma2 x y (iS i0) = y
  lemma2 x y (iS (iS v)) = var v

  substitute : ∀{Γ₁ Γ₂ τ} → swap-ctx Γ₁ Γ₂ → Γ₂ ⊢ τ → Γ₁ ⊢ τ
  substitute c z = z
  substitute c (var x) = c x
  substitute c (s e) = s (substitute c e)
  substitute c (rec e₀ e₁ e) = rec (substitute c e₀) (substitute (lemma (lemma c)) e₁) (substitute c e)
  substitute c (lam e) = lam (substitute (lemma c) e)
  substitute c (ap e₁ e₂) = ap (substitute c e₁) (substitute c e₂)

  {- Dynamic semantics -}
  data _↦_ : ∀{τ} → ([] ⊢ τ) → ([] ⊢ τ) → Set where
    ap-e₁-step : ∀{τ τ₂} (e₁ e₁' : [] ⊢ arr τ₂ τ) (e₂ : [] ⊢ τ₂) → (e₁ ↦ e₁') 
                  → (ap e₁ e₂) ↦ (ap e₁' e₂)
    ap-lam-step  : ∀{τ₁ τ₂} (e₁ : (τ₁ :: []) ⊢ τ₂) (e₂ : [] ⊢ τ₁)
                  → ap (lam e₁) e₂ ↦ substitute (lemma1 e₂) e₁ 
    rec-e-step : ∀{τ} (e₀ : [] ⊢ τ) → (e₁ : (nat :: (τ :: [])) ⊢ τ) → (e e' : [] ⊢ nat) → (e ↦ e') 
                  → (rec e₀ e₁ e) ↦ (rec e₀ e₁ e')
    rec-z-step : ∀{τ} (e₀ : [] ⊢ τ) → (e₁ : (nat :: (τ :: [])) ⊢ τ) 
                  → (rec e₀ e₁ z) ↦ e₀
    rec-s-step : ∀{τ} (e : [] ⊢ nat) → (e₀ : [] ⊢ τ) → (e₁ : (nat :: (τ :: [])) ⊢ τ)
                  → rec e₀ e₁ (s e) ↦ substitute (lemma2 e (rec e₀ e₁ e)) e₁

  {- Proof of progress -}
  progress : ∀{τ} (e : [] ⊢ τ) → Either (Value e) (Σ ([] ⊢ τ) (λ e' → e ↦ e'))
  progress z = Inl z-value
  progress (var ())
  progress (s e) = Inl s-value
  progress (rec e₀ e₁ e) with progress e 
  progress (rec e₀ e₁ .z) | Inl z-value = Inr (e₀ , rec-z-step e₀ e₁)
  progress (rec e₀ e₁ (s e)) | Inl s-value = Inr (substitute (lemma2 e (rec e₀ e₁ e)) e₁ , rec-s-step e e₀ e₁)
  progress (rec e₀ e₁ e) | Inr (e' , e↦e') = Inr (rec e₀ e₁ e' , rec-e-step e₀ e₁ e e' e↦e')
  progress (lam e) = Inl (lam-value e)
  progress (ap e₁ e₂) with progress e₁
  progress (ap .(lam e₁') e₂) | Inl (lam-value e₁') = Inr (substitute (lemma1 e₂) e₁' , ap-lam-step e₁' e₂ )
  progress (ap e₁ e₂) | Inr (e₁' , e₁↦e₁') = Inr (ap e₁' e₂ , ap-e₁-step e₁ e₁' e₂ e₁↦e₁')
