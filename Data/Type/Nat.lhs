> {-# LANGUAGE PolyKinds #-}
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
> import Data.Kind

> type family (n :: Nat) :+ (m :: Nat) :: Nat where
>   Z     :+ m = m
>   (S n) :+ m = S (n :+ m)

> type family (n :: Nat) :* (m :: Nat) :: Nat where
>   Z     :* m = Z
>   (S n) :* m = m :+ (n :* m)

> type family Pred (n :: Nat) :: Nat where
>   Pred Z     = Z
>   Pred (S n) = n

> type family (n :: Nat) :- (m :: Nat) :: Nat where
>   Z     :- m     = Z
>   n     :- Z     = n
>   (S n) :- (S m) = n :- m

> addSing :: SNat n -> SNat m -> SNat (n :+ m)
> addSing  SZ    m = m
> addSing (SS n) m = SS $ addSing n m

> mulSing :: SNat n -> SNat m -> SNat (n :* m)
> mulSing  SZ    m = SZ
> mulSing (SS n) m = m `addSing` mulSing n m

TODO: pasar a singletons

> data SNat (n :: Nat) where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

> class KnownNat (n :: Nat) where
>  natSing :: SNat n

> instance KnownNat Z where
>  natSing = SZ
> instance KnownNat n => KnownNat (S n) where
>  natSing = SS natSing

--
Al escribir esto estoy pensando en que en las pruebas voy a usar
Singleton solo si es necesario hacer pattern matching o llamar
recursivamente, sino mando Proxy. Pero si el cliente tiene
Singletons, que extraiga facil el Proxy.
Igual la dejo más general..

> proxyFrom :: forall (f :: k -> Type) (a :: k) . f a -> Proxy a
> proxyFrom _ = Proxy
 
---
Pruebas usando singleton. seguramente sea mas eficiente hacerlas con
type classes y proxies, para no generar los valores (aunque igual en
el core se generan las cadenas de cases).

> mzProof :: forall m . SNat m -> m :~: (m :+ Z) 
> mzProof  SZ     = Refl
> mzProof (SS n) = cong $ mzProof n

> msProof :: forall m n . SNat m -> Proxy (S n) -> (m :+ S n) :~: S (m :+ n)
> msProof SZ _     = Refl
> msProof (SS m) n = cong $ msProof m n 

> cong :: (x :: Nat) :~: (y :: Nat) -> (f x :: Nat) :~: (f y :: Nat)
> cong Refl = Refl

asi seria con clases:

> class LemmaProof (m :: Nat) where
>  lemmaSumSucc :: Proxy m -> Proxy (S n) ->  (m :+ S n)  :~: S (m :+ n)
>
> instance LemmaProof Z where
>  lemmaSumSucc _ _ = Refl

> instance LemmaProof m => LemmaProof (S m) where
>  lemmaSumSucc m n = cong $ lemmaSumSucc (prev m) n  

> prev :: Proxy (S n) -> Proxy n
> prev _ = Proxy

Voy a seguir un criterio de nombres para los teoremas, por eso algunos
teoremas pisan los anteriores, ademas pongo la expresión objetivo a
la izquierda de la igualdad:

> th_add_Z_r :: forall n . SNat n -> (n :+ Z) :~: n
> th_add_Z_r SZ = Refl
> th_add_Z_r (SS n) = cong $ th_add_Z_r n


Pruebas como la siguiente no las vamos a usar nunca, el typechecker se
encarga porque salen computando la TF, pero las agrego igual, por completitud:

> th_add_Z_l :: forall n . (Z :+ n) :~: n
> th_add_Z_l = Refl

> th_add_S_l :: forall n m . SNat n -> Proxy m -> (S n) :+ m :~: S (n :+ m) 
> th_add_S_l SZ _     = Refl
> th_add_S_l (SS n) _ = Refl

> th_add_S_r :: forall n m . SNat n -> Proxy m -> n :+ (S m) :~: S (n :+ m)
> th_add_S_r SZ p     = Refl
> th_add_S_r (SS n) p = cong $ th_add_S_r n p

> th_mul_Z_l :: Z :* n :~: Z
> th_mul_Z_l = Refl

> th_mul_Z_r :: SNat n -> n :* Z :~: Z
> th_mul_Z_r SZ     = Refl
> th_mul_Z_r (SS n) = th_mul_Z_r n

> th_mul_S_l :: SNat n -> SNat m -> S n :* m :~: n :* m :+ m 
> th_mul_S_l  SZ    m      = th_add_Z_r m
> th_mul_S_l (SS n) SZ     = let lem = th_mul_Z_r n
>                            in gcastWith lem Refl
> th_mul_S_l (SS n) m = let ih = th_mul_S_l n m
>                           aux = (th_add_comm m
>                                  (m `addSing` (n `mulSing` m)))
>                       in  gcastWith aux Refl

> th_add_comm :: forall n m . SNat n -> SNat m -> n :+ m :~: m :+ n
> th_add_comm SZ m     = sym $ th_add_Z_r m
> th_add_comm (SS n) m = let lem = sym $ th_add_S_r m $ proxyFrom n
>                            ih  = th_add_comm n m
>                        in  gcastWith ih lem

> th_add_assoc :: forall n m k . SNat n -> Proxy m -> Proxy k
>              -> n :+ m :+ k :~: n :+ (m :+ k)
> th_add_assoc  SZ    m k = Refl
> th_add_assoc (SS n) m k = let ih = th_add_assoc n m k
>                           in  cong ih

