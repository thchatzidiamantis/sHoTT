# 2-Segal spaces

Experimental formalization project on 2-Segal spaces.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume funext : FunExt
-- #assume weakextext : WeakExtExt
#assume extext : ExtExt
```

### The 3 dimensional 2-Segal horns

```rzk
#def Λ³₍₀₂₎
  : Δ³ → TOPE
  :=
    \ ((t1 , t2) , t3) → t3 ≡ 0₂ ∨ t1 ≡ t2 -- This could be t3==t2.

#def Λ³₍₁₃₎
  : Δ³ → TOPE
  :=
    \ ((t1 , t2) , t3) → t2 ≡ t3 ∨ t1 ≡ 1₂ -- This could be t1==t2.

#def 3-horn-restriction₍₀₂₎
  ( A : U)
  : ( Δ³ → A) → (Λ³₍₀₂₎ → A)
  := \ f t → f t

#def 3-horn-restriction₍₁₃₎
  ( A : U)
  : ( Δ³ → A) → (Λ³₍₁₃₎ → A)
  := \ f t → f t
```

### 2-Segal types

We use the conventions from the definition of `#!rzk hom3` from
`11-adjunctions.rzk`.

```rzk
#def is-2-segal₍₀₂₎
  ( A : U)
  : U
  :=
    ( w : A) → (x : A) → (y : A) → (z : A)
  → ( f : hom A w x) → (gf : hom A w y) → (hgf : hom A w z)
  → ( g : hom A x y) → (h : hom A y z)
  → ( α₃ : hom2 A w x y f g gf) → (α₁ : hom2 A w y z gf h hgf)
  → is-contr
      ( Σ ( hg : hom A x z)
      , ( Σ ( α₂ : hom2 A w x z f hg hgf)
        , ( Σ ( α₀ : hom2 A x y z g h hg)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))

#def is-2-segal₍₁₃₎
  ( A : U)
  : U
  :=
    ( w : A) → (x : A) → (y : A) → (z : A)
  → ( f : hom A w x) → (hgf : hom A w z)
  → ( g : hom A x y) → (hg : hom A x z) → (h : hom A y z)
  → ( α₂ : hom2 A w x z f hg hgf) → (α₀ : hom2 A x y z g h hg)
  → is-contr
      ( Σ ( gf : hom A w y)
      , ( Σ ( α₃ : hom2 A w x y f g gf)
        , ( Σ ( α₁ : hom2 A w y z gf h hgf)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))

#def is-2-segal
  ( A : U)
  : U
  :=
    product (is-2-segal₍₀₂₎ A) (is-2-segal₍₁₃₎ A)
```

```rzk
#def 3horn₍₀₂₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( h : hom A y z)
  ( α₃ : hom2 A w x y f g gf)
  ( α₁ : hom2 A w y z gf h hgf)
  : Λ³₍₀₂₎ → A
  :=
    \ ((t₁ , t₂) , t₃) →
      recOR
        ( t₃ ≡ 0₂ ↦ α₃ (t₁ , t₂)
        , t₁ ≡ t₂ ↦ α₁ (t₁ , t₃)) -- This could be t3==t2.

#def 3horn₍₁₃₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( hg : hom A x z)
  ( h : hom A y z)
  ( α₂ : hom2 A w x z f hg hgf)
  ( α₀ : hom2 A x y z g h hg)
  : Λ³₍₁₃₎ → A
  :=
  \ ((t₁ , t₂) , t₃) →
    recOR
      ( t₂ ≡ t₃ ↦ α₂ (t₁ , t₃) -- This could be t1==t2.
      , t₁ ≡ 1₂ ↦ α₀ (t₂ , t₃))

#def associators-are-3horn-fillings₍₀₂₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( h : hom A y z)
  ( α₃ : hom2 A w x y f g gf)
  ( α₁ : hom2 A w y z gf h hgf)
  : Equiv
      ( Σ ( hg : hom A x z)
      , ( Σ ( α₂ : hom2 A w x z f hg hgf)
        , ( Σ ( α₀ : hom2 A x y z g h hg)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))
      ( ( t : Δ³) → A [Λ³₍₀₂₎ t ↦ 3horn₍₀₂₎ A w x y z f gf hgf g h α₃ α₁ t])
  :=
    ( \ H t → second (second (second H)) t
      , ( ( ( \ k → (\ t → k ((1₂ , t) , t)
          , ( \ (t , s) → k ((t , s) , s)
            , ( \ (t , s) → k ((1₂ , t) , s)
              , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
          , \ H → refl))
        , ( ( \ k → (\ t → k ((1₂ , t) , t)
            , ( \ (t , s) → k ((t , s) , s)
              , ( \ (t , s) → k ((1₂ , t) , s)
                , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
            , \ H → refl))))

#def associators-are-3horn-fillings₍₁₃₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( hg : hom A x z)
  ( h : hom A y z)
  ( α₂ : hom2 A w x z f hg hgf)
  ( α₀ : hom2 A x y z g h hg)
  : Equiv
      ( Σ ( gf : hom A w y)
      , ( Σ ( α₃ : hom2 A w x y f g gf)
        , ( Σ ( α₁ : hom2 A w y z gf h hgf)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))
      ( ( t : Δ³) → A [Λ³₍₁₃₎ t ↦ 3horn₍₁₃₎ A w x y z f hgf g hg h α₂ α₀ t])
  :=
    ( \ H t → second (second (second H)) t
      , ( ( ( \ k → (\ t → k ((t , t) , 0₂)
          , ( \ (t , s) → k ((t , s) , 0₂)
            , ( \ (t , s) → k ((t , t) , s)
              , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
          , \ H → refl))
        , ( ( \ k → (\ t → k ((t , t) , 0₂)
            , ( \ (t , s) → k ((t , s) , 0₂)
              , ( \ (t , s) → k ((t , t) , s)
                , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
            , \ H → refl))))
```

A type is 2-Segal if and only if its based hom-types are Segal (hopefully).

```rzk
#def hom-coslice-hom2
  ( A : U)
  ( w x y : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  : ( Σ ( g : hom A x y) , (hom2 A w x y f g gf))
  → hom (coslice A w) (x , f) (y , gf)
  :=
    \ (g , α₃) t →
      ( g t
      , \ s →
          recOR
            ( s ≤ t ↦ gf s
            , t ≤ s ↦ α₃ (s , t)))

-- #def cofibration-union-432
--   ( A : U)
--   ( w x y : A)
--   ( f : hom A w x)
--   ( gf : hom A w y)
--   : U
--   :=
--     cofibration-union
--       ( 2 × 2)
--       ( \ (s , t) → s ≤ t)
--       ( \ ( s , t) → t ≤ s)
--       ()
--       ()

-- #def hom2-hom-coslice
--   ( A : U)
--   ( w x y : A)
--   ( f : hom A w x)
--   ( gf : hom A w y)
--   : hom (coslice A w) (x , f) (y , gf)
--   → ( Σ ( g : hom A x y) , (hom2 A w x y f g gf))
--   :=
--     \ G →
--       ( \ t → first (G t)
--       , \ (t , s) → (second (G s)) t)
```

### Characterizing 2-Segal types

A type is 2-Segal if and only if it is local with respect to both 2-Segal horn
inclusions.

```rzk
#def is-local-2-segal-horn-inclusion
  ( A : U)
  : U
  :=
    product
     ( is-local-type (2 × 2 × 2) Δ³ Λ³₍₀₂₎ A)
     ( is-local-type (2 × 2 × 2) Δ³ Λ³₍₁₃₎ A)

#def equiv-2-segal-horn-restriction₍₀₂₎
  ( A : U)
  : Equiv
    ( Δ³ → A)
    ( Σ ( k : Λ³₍₀₂₎ → A)
      , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
          , ( Σ ( α₂ : hom2
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( hg)
                        ( \ t → k ((t , t) , t)))
              , ( Σ ( α₀ : hom2
                            ( A)
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( hg))
                  , ( hom3
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( \ t → k ((t , t) , 0₂))
                        ( \ t → k ((t , t) , t))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( hg)
                        ( \ t → k ((1₂ , 1₂) , t))
                        ( \ (t , s) → k ((t , s) , 0₂))
                        ( α₂)
                        ( \ (t , s) → k ((t , t) , s))
                        ( α₀))))))
  :=
    ( \ H →
      ( ( ( ( ( \ t → H t)
        , ( ( ( \ t → H ((1₂ , t) , t))
          , ( ( ( \ (t , s) → H ((t , s) , s))
            , ( ( \ (t , s) → H ((1₂ , t) , s)
              , ( H)))))))))))
      , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl)
        , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl))))

#def equiv-2-segal-horn-restriction₍₁₃₎
  ( A : U)
  : Equiv
    ( Δ³ → A)
    ( Σ ( k : Λ³₍₁₃₎ → A)
      , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
          , ( Σ ( α₃ : hom2
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( gf))
              , ( Σ ( α₁ : hom2
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( gf)
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( \ t → k ((t , t) , t)))
                  , ( hom3
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( gf)
                        ( \ t → k ((t , t) , t))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( \ t → k ((1₂ , t) , t))
                        ( \ t → k ((1₂ , 1₂) , t))
                        ( α₃)
                        ( \ (t , s) → k ((t , s) , s))
                        ( α₁)
                        ( \ (t , s) → k ((1₂ , t) , s)))))))
  :=
    ( \ H →
      ( ( ( ( ( \ t → H t)
        , ( ( ( \ t → H ((t , t) , 0₂))
          , ( ( ( \ (t , s) → H ((t , s) , 0₂))
            , ( ( \ (t , s) → H ((t , t) , s)
              , ( H)))))))))))
      , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl)
        , ( ( \ G t → second (second (second (second (G)))) t , \ H → refl))))

#def equiv-2-segal-horn-restriction₍₀₂₎-is-2-segal₍₀₂₎
  ( A : U)
  ( is-2-segal₍₀₂₎-A : is-2-segal₍₀₂₎ A)
  : Equiv (Δ³ → A) (Λ³₍₀₂₎ → A)
  :=
    equiv-comp
      ( Δ³ → A)
      ( Σ ( k : Λ³₍₀₂₎ → A)
        , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
          , ( Σ ( α₂ : hom2
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( hg)
                        ( \ t → k ((t , t) , t)))
              , ( Σ ( α₀ : hom2
                            ( A)
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( hg))
                  , ( hom3
                        ( A)
                        ( k ((0₂ , 0₂) , 0₂))
                        ( k ((1₂ , 0₂) , 0₂))
                        ( k ((1₂ , 1₂) , 0₂))
                        ( k ((1₂ , 1₂) , 1₂))
                        ( \ t → k ((t , 0₂) , 0₂))
                        ( \ t → k ((t , t) , 0₂))
                        ( \ t → k ((t , t) , t))
                        ( \ t → k ((1₂ , t) , 0₂))
                        ( hg)
                        ( \ t → k ((1₂ , 1₂) , t))
                        ( \ (t , s) → k ((t , s) , 0₂))
                        ( α₂)
                        ( \ (t , s) → k ((t , t) , s))
                        ( α₀))))))
      ( Λ³₍₀₂₎ → A)
      ( equiv-2-segal-horn-restriction₍₀₂₎ A)
      ( projection-total-type
        ( Λ³₍₀₂₎ → A)
        ( \ k →
          ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
            , ( Σ ( α₂ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( hg)
                          ( \ t → k ((t , t) , t)))
                , ( Σ ( α₀ : hom2
                              ( A)
                              ( k ((1₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( \ t → k ((1₂ , t) , 0₂))
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( hg))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((t , t) , 0₂))
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( hg)
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( \ (t , s) → k ((t , s) , 0₂))
                          ( α₂)
                          ( \ (t , s) → k ((t , t) , s))
                          ( α₀))))))
      , ( is-equiv-projection-contractible-fibers
          ( Λ³₍₀₂₎ → A)
          ( \ k →
            ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
              , ( Σ ( α₂ : hom2
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( hg)
                            ( \ t → k ((t , t) , t)))
                  , ( Σ ( α₀ : hom2
                                ( A)
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( hg))
                      , ( hom3
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( \ t → k ((t , t) , 0₂))
                            ( \ t → k ((t , t) , t))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( hg)
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( \ (t , s) → k ((t , s) , 0₂))
                            ( α₂)
                            ( \ (t , s) → k ((t , t) , s))
                            ( α₀))))))
          ( \ k →
            is-2-segal₍₀₂₎-A
              ( k ((0₂ , 0₂) , 0₂))
              ( k ((1₂ , 0₂) , 0₂))
              ( k ((1₂ , 1₂) , 0₂))
              ( k ((1₂ , 1₂) , 1₂))
              ( \ t → k ((t , 0₂) , 0₂))
              ( \ t → k ((t , t) , 0₂))
              ( \ t → k ((t , t) , t))
              ( \ t → k ((1₂ , t) , 0₂))
              ( \ t → k ((1₂ , 1₂) , t))
              ( \ (t , s) → k ((t , s) , 0₂))
              ( \ (t , s) → k ((t , t) , s)))))

#def is-local-2-segal-horn-inclusion-is-2-segal₍₀₂₎
  ( A : U)
  ( is-2-segal₍₀₂₎-A : is-2-segal₍₀₂₎ A)
  : is-local-type (2 × 2 × 2) Δ³ Λ³₍₀₂₎ A
  :=
    second
      ( equiv-2-segal-horn-restriction₍₀₂₎-is-2-segal₍₀₂₎ A is-2-segal₍₀₂₎-A)

#def equiv-2-segal-horn-restriction₍₁₃₎-is-2-segal₍₁₃₎
  ( A : U)
  ( is-2-segal₍₁₃₎-A : is-2-segal₍₁₃₎ A)
  : Equiv (Δ³ → A) (Λ³₍₁₃₎ → A)
  :=
    equiv-comp
      ( Δ³ → A)
      ( Σ ( k : Λ³₍₁₃₎ → A)
        , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
            , ( Σ ( α₃ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( gf))
                , ( Σ ( α₁ : hom2
                              ( A)
                              ( k ((0₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( gf)
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( \ t → k ((t , t) , t)))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( gf)
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( \ t → k ((1₂ , t) , t))
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( α₃)
                          ( \ (t , s) → k ((t , s) , s))
                          ( α₁)
                          ( \ (t , s) → k ((1₂ , t) , s)))))))
      ( Λ³₍₁₃₎ → A)
      ( equiv-2-segal-horn-restriction₍₁₃₎ A)
      ( projection-total-type
        ( Λ³₍₁₃₎ → A)
        ( \ k →
          ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
            , ( Σ ( α₃ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( gf))
                , ( Σ ( α₁ : hom2
                              ( A)
                              ( k ((0₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( gf)
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( \ t → k ((t , t) , t)))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( gf)
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( \ t → k ((1₂ , t) , t))
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( α₃)
                          ( \ (t , s) → k ((t , s) , s))
                          ( α₁)
                          ( \ (t , s) → k ((1₂ , t) , s)))))))
      , ( is-equiv-projection-contractible-fibers
          ( Λ³₍₁₃₎ → A)
          ( \ k →
            ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
              , ( Σ ( α₃ : hom2
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( gf))
                  , ( Σ ( α₁ : hom2
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( gf)
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( \ t → k ((t , t) , t)))
                      , ( hom3
                            ( A)
                            ( k ((0₂ , 0₂) , 0₂))
                            ( k ((1₂ , 0₂) , 0₂))
                            ( k ((1₂ , 1₂) , 0₂))
                            ( k ((1₂ , 1₂) , 1₂))
                            ( \ t → k ((t , 0₂) , 0₂))
                            ( gf)
                            ( \ t → k ((t , t) , t))
                            ( \ t → k ((1₂ , t) , 0₂))
                            ( \ t → k ((1₂ , t) , t))
                            ( \ t → k ((1₂ , 1₂) , t))
                            ( α₃)
                            ( \ (t , s) → k ((t , s) , s))
                            ( α₁)
                            ( \ (t , s) → k ((1₂ , t) , s)))))))
          ( \ k →
            is-2-segal₍₁₃₎-A
              ( k ((0₂ , 0₂) , 0₂))
              ( k ((1₂ , 0₂) , 0₂))
              ( k ((1₂ , 1₂) , 0₂))
              ( k ((1₂ , 1₂) , 1₂))
              ( \ t → k ((t , 0₂) , 0₂))
              ( \ t → k ((t , t) , t))
              ( \ t → k ((1₂ , t) , 0₂))
              ( \ t → k ((1₂ , t) , t))
              ( \ t → k ((1₂ , 1₂) , t))
              ( \ (t , s) → k ((t , s) , s))
              ( \ (t , s) → k ((1₂ , t) , s)))))

#def is-local-2-segal-horn-inclusion-is-2-segal₍₁₃₎
  ( A : U)
  ( is-2-segal₍₁₃₎-A : is-2-segal₍₁₃₎ A)
  : is-local-type (2 × 2 × 2) Δ³ Λ³₍₁₃₎ A
  :=
    second
      ( equiv-2-segal-horn-restriction₍₁₃₎-is-2-segal₍₁₃₎ A is-2-segal₍₁₃₎-A)

#def is-local-2-segal-horn-inclusion-is-2-segal
  ( A : U)
  ( is-2-segal-A : is-2-segal A)
  : is-local-2-segal-horn-inclusion A
  :=
    ( is-local-2-segal-horn-inclusion-is-2-segal₍₀₂₎ A (first (is-2-segal-A))
    , is-local-2-segal-horn-inclusion-is-2-segal₍₁₃₎ A (second (is-2-segal-A)))
```

The converse direction: A type that is local with respect to the 2-Segal horn
inclusions in 2-Segal.

```rzk
#def is-2-segal-is-local-2-segal-horn-inclusion₍₀₂₎
  ( A : U)
  ( is-local-A : is-local-type (2 × 2 × 2) Δ³ Λ³₍₀₂₎ A)
  : is-2-segal₍₀₂₎ A
  :=
    \ w x y z f gf hgf g h α₃ α₁ →
      contractible-fibers-is-equiv-projection
        ( Λ³₍₀₂₎ → A)
        ( \ k →
          ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
            , ( Σ ( α₂ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( hg)
                          ( \ t → k ((t , t) , t)))
                , ( Σ ( α₀ : hom2
                              ( A)
                              ( k ((1₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( \ t → k ((1₂ , t) , 0₂))
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( hg))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((t , t) , 0₂))
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( hg)
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( \ (t , s) → k ((t , s) , 0₂))
                          ( α₂)
                          ( \ (t , s) → k ((t , t) , s))
                          ( α₀))))))
        ( second
          ( equiv-comp
            ( Σ ( k : Λ³₍₀₂₎ → A)
              , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
                  , ( Σ ( α₂ : hom2
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( hg)
                                ( \ t → k ((t , t) , t)))
                      , ( Σ ( α₀ : hom2
                                    ( A)
                                    ( k ((1₂ , 0₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 1₂))
                                    ( \ t → k ((1₂ , t) , 0₂))
                                    ( \ t → k ((1₂ , 1₂) , t))
                                    ( hg))
                          , ( hom3
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( \ t → k ((t , t) , 0₂))
                                ( \ t → k ((t , t) , t))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( hg)
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( \ (t , s) → k ((t , s) , 0₂))
                                ( α₂)
                                ( \ (t , s) → k ((t , t) , s))
                                ( α₀))))))
            ( Δ³ → A)
            ( Λ³₍₀₂₎ → A)
            ( inv-equiv
              ( Δ³ → A)
              ( Σ ( k : Λ³₍₀₂₎ → A)
                , ( Σ ( hg : hom A (k ((1₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 1₂)))
                    , ( Σ ( α₂ : hom2
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 1₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( hg)
                                  ( \ t → k ((t , t) , t)))
                        , ( Σ ( α₀ : hom2
                                      ( A)
                                      ( k ((1₂ , 0₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 1₂))
                                      ( \ t → k ((1₂ , t) , 0₂))
                                      ( \ t → k ((1₂ , 1₂) , t))
                                      ( hg))
                            , ( hom3
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 1₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( \ t → k ((t , t) , 0₂))
                                  ( \ t → k ((t , t) , t))
                                  ( \ t → k ((1₂ , t) , 0₂))
                                  ( hg)
                                  ( \ t → k ((1₂ , 1₂) , t))
                                  ( \ (t , s) → k ((t , s) , 0₂))
                                  ( α₂)
                                  ( \ (t , s) → k ((t , t) , s))
                                  ( α₀))))))
              ( equiv-2-segal-horn-restriction₍₀₂₎ A))
            ( \ f t → f t , is-local-A)))
        ( 3horn₍₀₂₎ A w x y z f gf hgf g h α₃ α₁)

#def is-2-segal-is-local-2-segal-horn-inclusion₍₁₃₎
  ( A : U)
  ( is-local-A : is-local-type (2 × 2 × 2) Δ³ Λ³₍₁₃₎ A)
  : is-2-segal₍₁₃₎ A
  :=
    \ w x y z f hgf g hg h α₂ α₀ →
      contractible-fibers-is-equiv-projection
        ( Λ³₍₁₃₎ → A)
        ( \ k →
          ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
            , ( Σ ( α₃ : hom2
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( gf))
                , ( Σ ( α₁ : hom2
                              ( A)
                              ( k ((0₂ , 0₂) , 0₂))
                              ( k ((1₂ , 1₂) , 0₂))
                              ( k ((1₂ , 1₂) , 1₂))
                              ( gf)
                              ( \ t → k ((1₂ , 1₂) , t))
                              ( \ t → k ((t , t) , t)))
                    , ( hom3
                          ( A)
                          ( k ((0₂ , 0₂) , 0₂))
                          ( k ((1₂ , 0₂) , 0₂))
                          ( k ((1₂ , 1₂) , 0₂))
                          ( k ((1₂ , 1₂) , 1₂))
                          ( \ t → k ((t , 0₂) , 0₂))
                          ( gf)
                          ( \ t → k ((t , t) , t))
                          ( \ t → k ((1₂ , t) , 0₂))
                          ( \ t → k ((1₂ , t) , t))
                          ( \ t → k ((1₂ , 1₂) , t))
                          ( α₃)
                          ( \ (t , s) → k ((t , s) , s))
                          ( α₁)
                          ( \ (t , s) → k ((1₂ , t) , s)))))))
        ( second
          ( equiv-comp
            ( Σ ( k : Λ³₍₁₃₎ → A)
              , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
                  , ( Σ ( α₃ : hom2
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( gf))
                      , ( Σ ( α₁ : hom2
                                    ( A)
                                    ( k ((0₂ , 0₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 0₂))
                                    ( k ((1₂ , 1₂) , 1₂))
                                    ( gf)
                                    ( \ t → k ((1₂ , 1₂) , t))
                                    ( \ t → k ((t , t) , t)))
                          , ( hom3
                                ( A)
                                ( k ((0₂ , 0₂) , 0₂))
                                ( k ((1₂ , 0₂) , 0₂))
                                ( k ((1₂ , 1₂) , 0₂))
                                ( k ((1₂ , 1₂) , 1₂))
                                ( \ t → k ((t , 0₂) , 0₂))
                                ( gf)
                                ( \ t → k ((t , t) , t))
                                ( \ t → k ((1₂ , t) , 0₂))
                                ( \ t → k ((1₂ , t) , t))
                                ( \ t → k ((1₂ , 1₂) , t))
                                ( α₃)
                                ( \ (t , s) → k ((t , s) , s))
                                ( α₁)
                                ( \ (t , s) → k ((1₂ , t) , s)))))))
            ( Δ³ → A)
            ( Λ³₍₁₃₎ → A)
            ( inv-equiv
              ( Δ³ → A)
              ( Σ ( k : Λ³₍₁₃₎ → A)
                , ( Σ ( gf : hom A (k ((0₂ , 0₂) , 0₂)) (k ((1₂ , 1₂) , 0₂)))
                    , ( Σ ( α₃ : hom2
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 0₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( \ t → k ((1₂ , t) , 0₂))
                                  ( gf))
                        , ( Σ ( α₁ : hom2
                                      ( A)
                                      ( k ((0₂ , 0₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 0₂))
                                      ( k ((1₂ , 1₂) , 1₂))
                                      ( gf)
                                      ( \ t → k ((1₂ , 1₂) , t))
                                      ( \ t → k ((t , t) , t)))
                            , ( hom3
                                  ( A)
                                  ( k ((0₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 0₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 0₂))
                                  ( k ((1₂ , 1₂) , 1₂))
                                  ( \ t → k ((t , 0₂) , 0₂))
                                  ( gf)
                                  ( \ t → k ((t , t) , t))
                                  ( \ t → k ((1₂ , t) , 0₂))
                                  ( \ t → k ((1₂ , t) , t))
                                  ( \ t → k ((1₂ , 1₂) , t))
                                  ( α₃)
                                  ( \ (t , s) → k ((t , s) , s))
                                  ( α₁)
                                  ( \ (t , s) → k ((1₂ , t) , s)))))))
              ( equiv-2-segal-horn-restriction₍₁₃₎ A))
            ( \ f t → f t , is-local-A)))
        ( 3horn₍₁₃₎ A w x y z f hgf g hg h α₂ α₀)

#def is-2-segal-is-local-2-segal-horn-inclusion
  ( A : U)
  ( is-local-A : is-local-2-segal-horn-inclusion A)
  : is-2-segal A
  :=
    ( is-2-segal-is-local-2-segal-horn-inclusion₍₀₂₎ A (first (is-local-A))
    , is-2-segal-is-local-2-segal-horn-inclusion₍₁₃₎ A (second (is-local-A)))

#def is-2-segal-iff-is-local-2-segal-horn-inclusion
  ( A : U)
  : iff (is-2-segal A) (is-local-2-segal-horn-inclusion A)
  :=
    ( is-local-2-segal-horn-inclusion-is-2-segal A
    , is-2-segal-is-local-2-segal-horn-inclusion A)
```

The proof of `is-local-horn-inclusion-function-type` generalizes to types being
local with respect to an arbitrary subshape inclusion.

```rzk
#def subshape-restriction
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : U)
  : ( ψ → A) → (ϕ → A)
  := \ f t → f t

#def is-local-function-type-fiberwise-is-local
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : U)
  ( C : A → U)
  ( fiberwise-is-local-C : (x : A) → is-local-type I ψ ϕ (C x))
  : is-local-type I ψ ϕ ((x : A) → C x)
  :=
    is-equiv-triple-comp
      ( ψ → ((x : A) → C x))
      ( ( x : A) → ψ → C x)
      ( ( x : A) → ϕ → C x)
      ( ϕ → ((x : A) → C x))
      ( \ g x t → g t x) -- first equivalence
      ( second (flip-ext-fun
        ( I)
        ( ψ)
        ( \ t → BOT)
        ( A)
        ( \ t → C)
        ( \ t → recBOT)))
      ( \ h x t → h x t) -- second equivalence
      ( second (equiv-function-equiv-family
        ( funext)
        ( A)
        ( \ x → (ψ → C x))
        ( \ x → (ϕ → C x))
        ( \ x → (subshape-restriction I ψ ϕ (C x) , fiberwise-is-local-C x))))
      ( \ h t x → (h x) t) -- third equivalence
      ( second (flip-ext-fun-inv
        ( I)
        ( \ t → ϕ t)
        ( \ t → BOT)
        ( A)
        ( \ t → C)
        ( \ t → recBOT)))
```

Using this general form, we prove that (dependent) function types into a family
of 2-Segal types are 2-Segal.

```rzk
#def is-local-2-segal-horn-inclusion-function-type uses (funext)
  ( A : U)
  ( C : A → U)
  ( fiberwise-is-2-segal-A : (x : A) → is-local-2-segal-horn-inclusion (C x))
  : is-local-2-segal-horn-inclusion ((x : A) → C x)
  :=
    ( is-local-function-type-fiberwise-is-local
        ( 2 × 2 × 2)
        ( Δ³)
        ( Λ³₍₀₂₎)
        ( A)
        ( C)
        ( \ x → first (fiberwise-is-2-segal-A x))
    , is-local-function-type-fiberwise-is-local
        ( 2 × 2 × 2)
        ( Δ³)
        ( Λ³₍₁₃₎)
        ( A)
        ( C)
        ( \ x → second (fiberwise-is-2-segal-A x)))
```

We do the same for the proof of `is-local-horn-inclusion-extension-type`

```rzk
#def is-local-subshape-inclusion-extension-type uses (extext)
  ( I J : CUBE)
  ( χ : I → TOPE)
  ( ψ : J → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : χ → U)
  ( fiberwise-is-local-A : (s : χ) → is-local-type J ψ ϕ (A s))
  : is-local-type J ψ ϕ ((s : χ) → A s)
  :=
    is-equiv-triple-comp
      ( ψ → (s : χ) → A s)
      ( ( s : χ) → ψ → A s)
      ( ( s : χ) → ϕ → A s)
      ( ϕ → (s : χ) → A s)
      ( \ g s t → g t s)  -- first equivalence
      ( second
        ( fubini
          ( J)
          ( I)
          ( \ t → ψ t)
          ( \ t → BOT)
          ( χ)
          ( \ s → BOT)
          ( \ t s → A s)
          ( \ u → recBOT)))
      ( \ h s t → h s t) -- second equivalence
      ( second (equiv-extensions-equiv extext I χ (\ _ → BOT)
        ( \ s → ψ → A s)
        ( \ s → ϕ → A s)
        ( \ s → (subshape-restriction J ψ ϕ (A s) , fiberwise-is-local-A s))
        ( \ _ → recBOT)))
      ( \ h t s → (h s) t) -- third equivalence
      ( second
        ( fubini
          ( I)
          ( J)
          ( χ)
          ( \ s → BOT)
          ( \ t → ϕ t)
          ( \ t → BOT)
          ( \ s t → A s)
          ( \ u → recBOT)))

#def is-2-segal-extension-type uses (extext)
  ( I : CUBE)
  ( χ : I → TOPE)
  ( A : χ → U)
  ( fiberwise-is-2-segal-A : (s : χ) → is-local-2-segal-horn-inclusion (A s))
  : is-local-2-segal-horn-inclusion ((s : χ) → A s)
  :=
    ( is-local-subshape-inclusion-extension-type I
        ( 2 × 2 × 2)
        ( χ)
        ( Δ³)
        ( Λ³₍₀₂₎)
        ( A)
        ( \ x → first (fiberwise-is-2-segal-A x))
    , is-local-subshape-inclusion-extension-type I
        ( 2 × 2 × 2)
        ( χ)
        ( Δ³)
        ( Λ³₍₁₃₎)
        ( A)
        ( \ x → second (fiberwise-is-2-segal-A x)))
```
