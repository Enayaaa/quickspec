module QuickSpec.Pruning.Completion where

import QuickSpec.Base
import QuickSpec.Type
import QuickSpec.Utils
import QuickSpec.Pruning
import qualified QuickSpec.Pruning.KBC as KBC
import QuickSpec.Pruning.Equation
import QuickSpec.Pruning.Queue
import QuickSpec.Pruning.Rewrite
import QuickSpec.Pruning.Constraints
import QuickSpec.Base
import QuickSpec.Prop
import QuickSpec.Term
import QuickSpec.Signature
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Control.Monad
import qualified Data.Set as Set
import qualified Data.Rewriting.Rule as Rule
import Data.Maybe

newtype Completion =
  Completion {
    kbc       :: KBC }

type KBC = KBC.KBC PruningConstant PruningVariable

initialState :: Int -> Completion
initialState n =
  Completion {
    kbc       = KBC.initialState n }

liftKBC :: Monad m => StateT KBC m a -> StateT Completion m a
liftKBC m = do
  s <- get
  (x, ks) <- lift (runStateT m (kbc s))
  put s { kbc = ks }
  return x

localKBC :: Monad m => StateT KBC m a -> StateT Completion m a
localKBC m = do
  ks <- gets kbc
  lift (evalStateT m ks)

newAxiom :: Monad m => PropOf PruningTerm -> StateT Completion m ()
newAxiom ([] :=>: (t :=: u)) = do
  liftKBC $ do
    norm <- KBC.normaliser
    unless (norm emptyContext t == norm emptyContext u) $ do
      KBC.newEquation (unconstrained (t :==: u))
      while KBC.complete KBC.unpause

while :: Monad m => m Bool -> m () -> m ()
while cond m = do
  x <- cond
  when x $ do
    m
    while cond m

findRep :: Monad m => [PropOf PruningTerm] -> PruningTerm -> StateT Completion m (Maybe PruningTerm)
findRep axioms t =
  localKBC $ do
    sequence_ [ KBC.newEquation (unconstrained (t :==: u)) | [] :=>: t :=: u <- axioms ]
    KBC.complete
    norm <- KBC.normaliser
    let u = norm emptyContext t
    if t == u then return Nothing else return (Just u)

instance Pruner Completion where
  emptyPruner sig = initialState (maxTermSize_ sig)
  untypedRep      = findRep
  untypedAxiom    = newAxiom
  pruningReport   = KBC.report . kbc
