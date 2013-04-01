G52AFP Coursework 2 - Monadic Compiler
   
Samuel Leask psysl1@nottingham.ac.uk
Jonathan Sherry psyjs3@nottingham.ac.uk

Imports
-------

> import Data.List
> import Control.Monad.Writer 
> import Control.Monad.State
> import Control.Monad.Trans

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
>
> reduce                ::  Expr -> Expr
> reduce (Val x)        =   Val x
> reduce (Var c)        =   error "something went horribly wrong while reducing an expr tree!"
> reduce (App op x y)   =   Val (arithOpt op (getVal $ (reduce x)) (getVal $ (reduce y)))
>                           where
>                               getVal (Val x) = x


> compProg     ::  Prog -> WriterT Code (State Label) ()
> compProg pr  =   
>   case pr of
>       Assign v e  ->  do
>                           tell (compExpr e)
>                           tell [POP v]
>                           return ()

        If e a b    ->  do tell (compIf e a b)
       While e pr  ->  do tell (compWhile e pr)
       Seqn prs    ->  do tell (compSeqn prs)

 compIf       ::  Expr -> Prog -> Prog -> WriterT Code (State Label) ()
 compIf e a b =   do
                       l   <-  get
                       modify (+1)
                       l'  <-  get
                       true <- compProg a
                       false <- compProg b
                       tell (compExpr e)
                       tell [JUMPZ l]
                       tell true
                       tell [JUMP l', LABEL l]
                       tell false
                       tell [LABEL l']
                       return ()

 compWhile        ::  Expr -> Prog -> State Label ()
 compWhile e pr   = do
                       l   <- get
                       modify (+1)
                       l'  <- get
                       pr' <- compProg pr
                       return ([LABEL l] ++ (compExpr e) ++ [JUMPZ l'] ++ pr' ++ [JUMP l, LABEL l'])

 compWhile         ::  Expr -> Prog -> WriterT Code (State Label) ()
 compWhile e pr    =   do
                       l   <-  get
                       modify (+1)
                       l'  <-  get
                       pr' <-  compProg pr
                       tell [LABEL l]
                       tell (compExpr e)
                       tell [JUMPZ l']
                       tell pr'
                       tell [JUMP l, LABEL l']
                       return ()

 compSeqn          ::  [Prog] -> WriterT Code (State Label) ()
 compSeqn [pr]     =   compProg pr
 compSeqn (pr:prs) = do
                        compFirst <- compProg pr
                        compRest  <- compSeqn prs
                        tell compFirst
                        tell compRest
                        return ()

It's all wrong... ;_;
        
> comp      ::  Prog -> Code
> comp pr   =   snd $ fst $ runState (runWriterT $ compProg pr) 0



-----------------------------------------------------------------------
not monadic (but it probably shouldn't be anyway)

> type Counter = Int
> type Machine = (Code, Stack, Mem, Counter)

> loadVar          ::  Name -> Mem -> Int
> loadVar var mem  =   isLegit $ lookup var mem
>                           where
>                               isLegit (Just x)    = x
>                               isLegit Nothing     = error "var not found in memory!"

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
>                           Nothing     ->   error "something has gone badly wrong!"
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



> execStep                  ::  Machine -> Machine
> execStep (c, st, mem, pc) =    case (c !! pc) of
>                                   PUSH    n   ->  (c, (n:st), mem, (pc+1))
>                                   PUSHV   v   ->  (c, ((loadVar v mem):st), mem, (pc+1))
>                                   POP     v   ->  (c, (tail st), (storeVar v (head st) mem), (pc+1))
>                                   DO      op  ->  (c, (doOp op st), mem, (pc+1))
>                                   LABEL   l   ->  (c, st, mem, (pc+1))
>                                   JUMP    l   ->  (c, st, mem, (findLabel l c))
>                                   JUMPZ   l   ->  (c, (tail st), mem, (if (head st) == 0 then (findLabel l c) else (pc+1)))

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


