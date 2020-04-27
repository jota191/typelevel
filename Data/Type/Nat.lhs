> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE PatternSynonyms #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE ScopedTypeVariables #-}


> module Data.Type.Nat where
> import Data.Nat
> import Data.Type.Equality
> import Data.Proxy

> type family (m :: Nat) :+ (n :: Nat) :: Nat where
>   Z     :+ n = n
>   (S m) :+ n = S (m :+ n)

> type family (m :: Nat) :* (n :: Nat) :: Nat where
>   Z     :* n = Z
>   (S m) :* n = n :+ (m :* n)

TODO: pasar a singletons

> data SNat (n :: Nat) where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

> class KnownNat (n :: Nat) where
>  natSing :: SNat n
>
> instance KnownNat Z where
>  natSing = SZ
> instance KnownNat n => KnownNat (S n) where
>  natSing = SS natSing


pruebas usando singleton. seguramente sea mas eficiente hacerlas con
type classes y proxies, para no generar los valores (aunque igual en
el core se generan las cadenas de cases).

> mzProof :: forall m . SNat m -> m :~: (m :+ Z) 
> mzProof  SZ     = Refl
> mzProof (SS n) = cong $ mzProof n

> msProof :: forall m n . SNat m -> Proxy (S n) ->  (m :+ S n)  :~: S (m :+ n)
> msProof SZ _     = Refl
> msProof (SS m) n = cong $ msProof m n 

> cong :: (x :: Nat) :~: (y :: Nat) -> (f x :: Nat) :~: (f y :: Nat)
> cong Refl = Refl
