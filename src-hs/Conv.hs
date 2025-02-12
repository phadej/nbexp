module Conv where

import Data.Kind (Constraint, Type)
import Data.SOP (NP (..))
import Data.Type.Equality ((:~:) (..), (:~~:) (..))
import Type.Reflection (TypeRep, Typeable, eqTypeRep, typeRep)

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data Ty
    = Fun Ty Ty
    | Emp
  deriving Show

type a ~> b = Fun a b
infixr 0 ~>

type Ctx = [Ty]

-- For convenience, we'll use Typeable as singleton for types.
type STy :: Ty -> Type
type STy a = TypeRep a

type STyI :: Ty -> Constraint
type STyI a = Typeable a

sty :: STyI a => STy a
sty = typeRep

-------------------------------------------------------------------------------
-- de Bruijn
-------------------------------------------------------------------------------

type Idx :: [k] -> k -> Type
data Idx xs a where
    IZ :: Idx (a : xs) a
    IS :: Idx xs a -> Idx (b : xs) a

deriving instance Show (Idx xs a)

lookupNP :: NP f xs -> Idx xs x -> f x
lookupNP Nil       x      = case x of {}
lookupNP (x :* _)  IZ     = x
lookupNP (_ :* xs) (IS i) = lookupNP xs i

type DB :: Ctx -> Ty -> Type
data DB ctx ty where
    DVar :: Idx ctx ty -> DB ctx ty
    DApp :: DB ctx (Fun a b) -> DB ctx a -> DB ctx b
    DLam :: STyI a => DB (a : ctx) b -> DB ctx (Fun a b)

deriving instance Show (DB ctx ty)

-------------------------------------------------------------------------------
-- PHOAS
-------------------------------------------------------------------------------

type PHOAS :: (Ty -> Type) -> Ty -> Type
data PHOAS var ty where
    PVar :: var ty -> PHOAS var ty
    PApp :: PHOAS var (Fun a b) -> PHOAS var a -> PHOAS var b
    PLam :: STyI a => (var a -> PHOAS var b) -> PHOAS var (Fun a b)

plam :: STyI a => (PHOAS var a -> PHOAS var b) -> PHOAS var (Fun a b)
plam f = PLam $ \x -> f (PVar x)

-------------------------------------------------------------------------------
-- de Bruijn to PHOAS
-------------------------------------------------------------------------------

toPHOAS :: NP var ctx -> DB ctx a -> PHOAS var a
toPHOAS env (DVar i)   = PVar (lookupNP env i)
toPHOAS env (DApp f t) = PApp (toPHOAS env f) (toPHOAS env t)
toPHOAS env (DLam t)   = PLam $ \x -> toPHOAS (x :* env) t

-------------------------------------------------------------------------------
-- PHOAS to de Bruijn
-------------------------------------------------------------------------------

-- We cannot really do the same as in Agda,
-- but we can get close.

-- a singleton for Ctx
type SCtx :: Ctx -> Type
data SCtx ctx where
    SNil  :: SCtx '[]
    SCons :: STy a -> SCtx ctx -> SCtx (a : ctx)

eqSCtx :: SCtx xs -> SCtx ys -> Maybe (xs :~: ys)
eqSCtx SNil SNil = Just Refl
eqSCtx (SCons x xs) (SCons y ys) = do
    HRefl <- eqTypeRep x y
    Refl <- eqSCtx xs ys
    return Refl
eqSCtx SNil SCons {} = Nothing
eqSCtx SCons {} SNil = Nothing

-- If you squint hard enough, this approach starts to look like ones in
-- Generic Conversions of Abstract Syntax Representations or
-- Unembedding Domain-Specific Languages
--
-- but it still resembles our Agda solution.
--
-- The difference is that we don't have well-formedness predicate,
-- but rather check well-formedness condition inside makeVar.
--
-- The drawback is that we need equality procedure on types.
-- In well-scoped representation we'd just compare lengths of contexts;
-- and we could compare the lengths here too, even strongly
-- relying on parametricity (and using unsafeCoerce).
--
type ToCtx :: Ty -> Type
data ToCtx a where
    ToCtx :: STy a -> SCtx ctx -> ToCtx a

deriving instance Show (ToCtx ctx)
deriving instance Show (SCtx ctx)

makeVar :: forall a sfx ctx. STy a -> SCtx sfx -> SCtx ctx -> Idx ctx a
makeVar a sfx ctx0 = go ctx0
  where
    go :: SCtx ctx' -> Idx ctx' a
    go SNil = error $ "Should not happen: " ++
        show (SCons a sfx) ++ " is not suffix of " ++ show ctx0
    go (SCons b ctx)
        | Just HRefl <- eqTypeRep a b
        , Just Refl <- eqSCtx sfx ctx
        = IZ

        | otherwise
        = IS (makeVar a sfx ctx)

toDB :: SCtx ctx -> PHOAS ToCtx a -> DB ctx a
toDB ctx (PVar (ToCtx a sfx)) = DVar (makeVar a sfx ctx)
toDB ctx (PApp f t)           = DApp (toDB ctx f) (toDB ctx t)
toDB ctx (PLam f)             = DLam (toDB (SCons sty ctx) (f (ToCtx sty ctx)))

-------------------------------------------------------------------------------
-- Example
-------------------------------------------------------------------------------

ex :: (Typeable a, Typeable b) => PHOAS v ((a ~> b) ~> a ~> b)
ex = plam $ \f -> plam $ \x -> PApp f x
