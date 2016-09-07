module Main

import Data.List

data Expr = Implication Expr Expr
          | Var String
          | Neg Expr

Eq Expr where
  (Implication e11 e12) == (Implication e21 e22) = e11 == e21 && e12 == e22
  (Var s1) == (Var s2) = s1 == s2
  (Neg e1) == (Neg e2) = e1 == e2
  _ == _ = False

data ExprSet = MKExprSet (List Expr) (List Expr) (List Expr)
data Sequent = MKSequent ExprSet ExprSet

mutual
  null : List a -> Bool
  null [] = True
  null _  = False
  
  emptyExprSet : ExprSet
  emptyExprSet = MKExprSet [] [] []
  
  getComposite : ExprSet -> List Expr
  getComposite (MKExprSet _ _ s) = s
  
  getAtoms : ExprSet -> List Expr
  getAtoms (MKExprSet a _ _) = a
  
  getNeg : ExprSet -> List Expr
  getNeg (MKExprSet _ n _) = n
  
  isEmpty : ExprSet -> Bool
  isEmpty (MKExprSet a b c) = (null a) && (null b) && (null c)
  
  canAddLK : ExprSet -> Bool
  canAddLK _ = True
  
  canAddLJ : ExprSet -> Bool
  canAddLJ = isEmpty
  
  getAll : ExprSet -> List Expr
  getAll (MKExprSet a n s) = a ++ n ++ s
  
  getLeftSide : Sequent -> List Expr
  getLeftSide (MKSequent (MKExprSet a n s) rhs) with (canAdd rhs)
   | True  = n ++ s
   | False = s
  
  addExpr : ExprSet -> Expr -> ExprSet
  addExpr (MKExprSet as ns cs) a@(Var _) = MKExprSet (a :: as) ns cs
  addExpr (MKExprSet as ns cs) n@(Neg _) = MKExprSet as (n :: ns) cs
  addExpr (MKExprSet as ns cs) c = MKExprSet as ns (c :: cs)
  
  removeExpr : ExprSet -> Expr -> ExprSet
  removeExpr (MKExprSet as ns cs) e = (MKExprSet (fn as) (fn ns) (fn cs))
    where fn = delete e
  
  isAxiom : Sequent -> Bool
  isAxiom (MKSequent lhs rhs) = (not $ isEmpty rhs) && (any (\y => any (== y) (getAll lhs)) $ getAll rhs)
  
  expandLeft : Sequent -> Expr -> Maybe (List Sequent)
  expandLeft s@(MKSequent lhs rhs) x@(Implication a b) =
    let nlhs = removeExpr lhs x
    in Just $ [MKSequent nlhs (addExpr emptyExprSet a),
               MKSequent (addExpr nlhs b) rhs]
  expandLeft s@(MKSequent lhs rhs) x@(Neg a) =
    if canAdd rhs
    then Just $ [MKSequent (removeExpr lhs x) (addExpr rhs a)]
    else Nothing
  
  expandRight : Sequent -> Expr -> Maybe (List Sequent)
  expandRight s@(MKSequent lhs rhs) x@(Implication a b) = Just $ [MKSequent (addExpr lhs a) (addExpr (removeExpr rhs x) b)]
  expandRight s@(MKSequent lhs rhs) x@(Neg a) = Just $ [MKSequent (addExpr lhs a) (removeExpr rhs x)]
  expandRight _ _ = Nothing
  
  stepLeft : Sequent -> Maybe (List Sequent)
  stepLeft s = listToMaybe $ mapMaybe (expandLeft s) (getLeftSide s)
  
  stepRight : Sequent -> Maybe (List Sequent)
  stepRight s@(MKSequent lhs rhs) = listToMaybe $ mapMaybe (expandRight s) ((getComposite rhs) ++ (getNeg rhs))
  
  -- Apply stepLeft, if that returns Nothing, apply stepRight.
  -- If both result in Nothing, return Nothing.
  stepLK : Sequent -> Maybe (List Sequent)
  stepLK s = listToMaybe $ catMaybes [stepLeft s, stepRight s]
  
  -- Like normal step, just that when there is a value on the
  -- right side, but no more steps can be taken and the sequent
  -- is not an axiom, drop the value on the right side and
  -- try again.
  stepLJ : Sequent -> Maybe (List Sequent)
  stepLJ s@(MKSequent lhs rhs) =
    let r = listToMaybe $ catMaybes [stepLeft s, stepRight s]
    in case r of
         Just x => Just x
         Nothing => if (isAxiom s) || (isEmpty rhs)
                    then Nothing
                    else Just $ [MKSequent lhs emptyExprSet]
  
  getFirst : (Maybe a, a) -> a
  getFirst ((Just x), _) = x
  getFirst (_, y) = y
  
  -- Run step on all sequents. If step returns Nothing for all of then
  -- also return nothing.
  steps : List Sequent -> Maybe (List Sequent)
  steps xs = if all (isNothing . fst) nextIter
             then Nothing
             else Just $ concat $ map getFirst nextIter
    where nextIter : List (Maybe (List Sequent), List Sequent)
          nextIter = map (\x => (step x, [x])) xs
  
  iterToNothing : (a -> Maybe a) -> a -> a
  iterToNothing fn x = case fn x of Nothing => x
                                    Just y  => iterToNothing fn y
  

  step : Sequent -> Maybe (List Sequent)
  step = stepLJ

  canAdd : ExprSet -> Bool  
  canAdd = canAddLJ
  
  -- Apply steps until it returns Nothing. That means that no more steps
  -- need to be run. Then check whether all sequents are axioms.
  solve : Sequent -> Bool
  solve s = all isAxiom $ iterToNothing steps [s]
  
  toExprSet : List Expr -> ExprSet
  toExprSet = foldl addExpr emptyExprSet

main : IO ()
main = putStrLn "hello sequent!"
