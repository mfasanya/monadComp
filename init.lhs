G52AFP Coursework 2 - Monadic Compiler
   
Samuel Leask psysl1@nottingham.ac.uk
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
>                          deriving (Show, Eq)
>
> type Name             =  Char
>
> data Op               =  Add | Sub | Mul | Div
>                          deriving (Show, Eq)


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
>       App op (Val a) (Val b)  ->  [PUSH (exprOpt op a b)]
>       App op a b              ->  (if (isReductible e) then (compExpr $ reduce e) else (compExpr a) ++ (compExpr b)) ++ [DO op]
>


Optimise out arithmetic operations where both arguments are known at compile-time (constant folding)

> exprOpt           ::  Op -> Int -> Int -> Int
> exprOpt op x y   
>                   |   x == y  = commonOpt op x
>                   |   otherwise = arithOpt op x y

> arithOpt          ::  Op -> Int -> Int -> Int
> arithOpt op x y   =
>   case op of
>       Add     ->      x + y
>       Sub     ->      x - y
>       Mul     ->      x * y
>       Div     ->      x `div` y

...and optimise for instances where the operands are equal.

> commonOpt         ::  Op -> Int -> Int
> commonOpt op  x   =
>   case op of
>       Add         ->  2*x
>       Sub         ->  0
>       Mul         ->  x^2
>       Div         ->  1

Determine whether an expr can be computed entirely at compile-time, exploiting the fact that such an expr-tree has only 'Val's at the leaves

> isReductible              ::  Expr    ->  Bool
> isReductible (Var _)      =   False
> isReductible (App _ x y)  =   (isReductible) x && (isReductible y)
> isReductible (Val x)      =   True

> reduce                ::  Expr -> Expr
> reduce (Val x)        =   Val x
> reduce (Var c)        =   error "something went horribly wrong while reducing an expr tree!"
> reduce (App op x y)   =   Val (arithOpt op (getVal $ (reduce x)) (getVal $ (reduce y)))
>                           where
>                               getVal (Val x) = x

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
        

> comp      ::  Prog -> Code
> comp pr   =   fst $ c 0
>                   where
>                       (ST c) = compProg' pr



-----------------------------------------------------------------------
not monadic (but it probably shouldn't be anyway)

> type Counter = Int
> type Machine = (Code, Stack, Mem, Counter)

> loadVar            ::  Name -> Mem -> Int
> loadVar var (m:ms) =   if (fst m) == var then (snd m) else loadVar var ms

> storeVar          ::  Name -> Int -> Mem -> Mem
> storeVar v n m    =   (v,n):m

> doOp              ::  Op -> Stack -> Stack
> doOp op (y:x:st)  =
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

> execLoop      ::  Machine -> Mem
> execLoop m    =   if (pc >= (length c)) then mem
>                       else
>                           execLoop (execStep m)
>                               where (c,_,mem,pc) = m



> execStep                      ::  Machine -> Machine
> execStep m@(c, st, mem, pc)   =    case (c !! pc) of
>                                       PUSH    n   ->  (c, (n:st), mem, (pc+1))
>                                       PUSHV   v   ->  (c, ((loadVar v mem):st), mem, (pc+1))
>                                       POP     v   ->  (c, (tail st), (storeVar v (head st) mem), (pc+1))
>                                       DO      op  ->  (c, (doOp op st), mem, (pc+1))
>                                       LABEL   l   ->  (c, st, mem, (pc+1))
>                                       JUMP    l   ->  (c, st, mem, (findLabel l c))
>                                       JUMPZ   l   ->  (c, (tail st), mem, (if (head st) == 0 then (findLabel l c) else (pc+1)))

> debugger      ::  Machine -> IO()
> debugger m    =   do
>                       putStrLn (show m)
>                       option <- getChar
>                       if (option == 'x') then return ()
>                           else
>                               do
>                                   let next = execStep m
>                                   debugger next

Execution

> exec	    ::	Code -> Mem
> exec c    =   reverse $ remDupes $ execLoop (c,[],[],0)

--------------------------------------------------------------------------

 readCode          ::  String  ->  IO [Inst]
 readCode  file    =   


