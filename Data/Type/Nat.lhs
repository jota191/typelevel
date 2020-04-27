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

> class ToSNat (n :: Nat) where
>  toSNat :: SNat n
>
> instance ToSNat Z where
>  toSNat = SZ
> instance ToSNat n => ToSNat (S n) where
>  toSNat = SS toSNat
