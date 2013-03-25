G52AFP Coursework 2 - Monadic Compiler
   
Samuel Leask -psysl1@nottingham.ac.uk
Jonathan Sherry psyjs3@nottingham.ac.uk

Imports
-------

> import Data.List


Imperative language
-------------------


> data Prog             =  Assign Name Expr
>                       |  If Expr Prog Prog
>                       |  While Expr Prog
>                       |  Seqn [Prog]
>                          deriving Show
>
> data Expr             =  Val Int | Var Name | App Op Expr Expr
>                          deriving Show
>
> type Name             =  Char
>
> data Op               =  Add | Sub | Mul | Div
>                          deriving Show


Virtual machine
---------------

> type Stack            =  [Int]
>
> type Mem              =  [(Name,Int)]
>
> type Code             =  [Inst]
>
> data Inst             =  PUSH Int
>                       |  PUSHV Name
>                       |  POP Name
>                       |  DO Op
>                       |  JUMP Label
>                       |  JUMPZ Label
>                       |  LABEL Label
>                          deriving Show
>
> type Label            =  Int


Factorial example
-----------------

> fac                   :: Int -> Prog
> fac n                 =  Seqn [Assign 'A' (Val 1),
>                                Assign 'B' (Val n),
>                                While (Var 'B') (Seqn
>                                   [Assign 'A' (App Mul (Var 'A') (Var 'B')),
>                                    Assign 'B' (App Sub (Var 'B') (Val 1))])]

-----------------------------------------------------------------------
Compilation


> compExpr      :: Expr -> Code
> compExpr e =
>   case e of
>       Val i                   ->  [PUSH i]
>       Var x                   ->  [PUSHV x]
>       App op (Val a) (Val b)  ->  [PUSH (arithOpt op a b)]
>       App op a b              ->  (compExpr a) ++ (compExpr b) ++ [DO op]


Optimise out arithmetic operations where both arguments are known at compile-time

> arithOpt      ::      Op -> Int -> Int -> Int
> arithOpt op x y =
>   case op of
>       Add     ->      x + y
>       Sub     ->      x - y
>       Mul     ->      x * y
>       Div     ->      x `div` y

NOT Monadic		 

> compIf            ::  Label -> Expr -> Prog -> Prog -> (Code, Label)
> compIf l e t f    =   ((compExpr e) ++ [JUMPZ l] ++ true ++ [JUMP l', LABEL l] ++ false ++ [LABEL l'], l'')
>                           where
>                               (true, l') = compProg t (l+1)
>                               (false, l'') = compProg f (l'+1)

> compWhile         ::  Label -> Expr -> Prog -> (Code, Label)
> compWhile l e pr  =   ([LABEL l] ++ (compExpr e) ++ [JUMPZ l'] ++ pr' ++ [JUMP l, LABEL l'], (l'+1))
>                           where
>                               (pr', l') = compProg pr (l+1)

> compSeq               ::  Label -> [Prog] -> (Code, Label)
> compSeq l [pr]        =   compProg pr l
> compSeq l (pr:prs)    =   (compFirst ++ compRest, l'')
>                               where
>                                   (compFirst, l') = compProg pr l
>                                   (compRest, l'') = compSeq l' prs

> compProg          ::  Prog -> Label -> (Code, Label)
> compProg pr l     =
>   case pr of
>       Assign n e  ->  ((compExpr e) ++ [POP n], l)
>       If e t f    ->  compIf l e t f
>       While e pr  ->  compWhile l e pr
>       Seqn prs    ->  compSeq l prs

 comp		::	Prog -> Code
 comp pr   =   fst $ compProg pr 0

Monadic, state is label

> type State    =   Label
> data ST a     =   ST (Label -> (a, Label))
> instance Monad ST where
>   return x         =   ST $ \s -> (x,s)
>   (ST st) >>= f    =   ST $ \s -> let (x,s')  = st s
>                                       (ST q)  = f x 
>                                   in q s'

> newLabel             ::  ST Label
> newLabel             =   ST (\n -> (n, n+1))

> compIf'       :: Expr -> Prog -> Prog -> ST Code
> compIf' e t f = do
>                   l       <- newLabel
>                   l'      <- newLabel
>                   true    <- compProg' t
>                   false   <- compProg' f
>                   return ((compExpr e) ++ [JUMPZ l] ++ true ++ [JUMP l', LABEL l] ++ false ++ [LABEL l'])

> compWhile'        ::  Expr -> Prog -> ST Code
> compWhile' e pr   = do
>                       l   <- newLabel
>                       l'  <- newLabel
>                       pr' <- compProg' pr
>                       return ([LABEL l] ++ (compExpr e) ++ [JUMPZ l'] ++ pr' ++ [JUMP l, LABEL l'])

> compSeqn'          ::  [Prog] -> ST Code
> compSeqn' [pr]     =   compProg' pr
> compSeqn' (pr:prs) = do
>                        compFirst <- compProg' pr
>                        compRest  <- compSeqn' prs
>                        return (compFirst ++ compRest)

> compProg'         ::  Prog -> ST Code
> compProg' pr      =
>   case pr of
>       Assign n e      -> do
>                           return $ (compExpr e) ++ [POP n] 
>
>       If e t f        -> compIf' e t f
>
>       While e pr      -> compWhile' e pr
>
>       Seqn prs        -> compSeqn' prs
        
Useful for debugging, delete before hand in.

> runComputation            :: ST Code -> (Code,Int)
> runComputation (ST c)     =  c 0

> comp      ::  Prog -> Code
> comp pr   =   fst $ c 0
>                   where
>                       (ST c) = compProg' pr



-----------------------------------------------------------------------
not monadic

> type Counter = Int
> type Machine = (Code, Stack, Mem, Counter)

> loadVar            ::  Name -> Mem -> Int
> loadVar var (m:ms) =   if (fst m) == var then (snd m) else loadVar var ms

> storeVar          ::  Name -> Int -> Mem -> Mem
> storeVar v n m    =   (v,n):m

> doOp              ::  Op -> Stack -> Stack
> doOp op (x:y:st)  =
>   case op of
>       Add         ->  (x + y):st
>       Sub         ->  (x - y):st
>       Mul         ->  (x * y):st
>       Div         ->  (x `div` y):st

> findLabel         ::  Label -> Code -> Counter
> findLabel l c     =   case (findIndex pred c) of
>                           Just x      ->   x
>                           Nothing     ->   error "Something has gone badly wrong!"
>                       where
>                           pred (LABEL l') = l' == l
>                           pred _          = False

> remDupes  ::  Mem -> Mem
> remDupes  =   nubBy (\(v, n) (v', n') -> v == v')

> execLoop                  ::  Machine -> Mem
> execLoop (c, st, mem, pc) =   if (pc >= (length c)) then (remDupes mem)
>                                 else 
>                                   case (c !! pc) of
>                                       PUSH    n   ->  execLoop (c, (n:st), mem, (pc+1))
>                                       PUSHV   v   ->  execLoop (c, ((loadVar v mem):st), mem, (pc+1))
>                                       POP     v   ->  execLoop (c, (tail st), (storeVar v (head st) mem), (pc+1))
>                                       DO      op  ->  execLoop (c, (doOp op st), mem, (pc+1))
>                                       LABEL   l   ->  execLoop (c, st, mem, pc+1)
>                                       JUMP    l   ->  execLoop (c, st, mem, (findLabel l c))
>                                       JUMPZ   l   ->  execLoop (c, st, mem, (if (head st) == 0 then (findLabel l c) else (pc+1)))



Execution

> exec	    ::	Code -> Mem
> exec c    =   execLoop (c,[],[],0)
