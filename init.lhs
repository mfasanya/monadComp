G52AFP Coursework 2 - Monadic Compiler
   
Samuel Leask psysl1@nottingham.ac.uk
Jonathan Sherry psyjs3@nottingham.ac.uk

Imports
-------

> import Data.List
> import Control.Monad.Writer 
> import Control.Monad.State
> import Control.Monad.Trans
> import Control.Monad.Reader

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


> type Mem              =  [(Name,Int)]
>
> type Stack            =  [Int]
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
>   case (optExpr True e) of
>       Val i                   ->  [PUSH i]
>       Var x                   ->  [PUSHV x]
>       App op a b              ->  (compExpr a) ++ (compExpr b) ++ [DO op]

Problem: needs one more step at the end to simplify again.  Returns exprs like (App Mul (Val 0) (Var 'x')). Difficult.
Solved:  absolutely disgusting

Problem: can improve simplification to allow this 2x - x = x

> optExpr       ::  Bool -> Expr -> Expr
> optExpr continue e =
>   case e of
>       Val _       ->  e
>       Var _       ->  e
>       App Add x y ->  stopOrNot $ addOpt x y
>       App Sub x y ->  stopOrNot $ subOpt x y
>       App Mul x y ->  stopOrNot $ mulOpt x y
>       App Div x y ->  stopOrNot $ divOpt x y
>   where
>       stopOrNot = if continue then optExpr (not continue) else id

> addOpt                    ::  Expr -> Expr -> Expr
> addOpt (Val 0) x          =   optExpr False x
> addOpt x (Val 0)          =   optExpr False x
> addOpt (Val x) (Val y)    =   Val (x + y)
> addOpt x y                =   if (x == y) then App Mul (Val 2) (optExpr False x) else App Add (optExpr False x) (optExpr False y)

> subOpt                    ::  Expr -> Expr -> Expr
> subOpt x (Val 0)          =   optExpr False x
> subOpt (Val x) (Val y)    =   Val (x - y)
> subOpt x y                =   if (x == y) then Val 0 else App Sub (optExpr False x) (optExpr False y)

> mulOpt                    ::  Expr -> Expr -> Expr
> mulOpt _ (Val 0)          =   Val 0
> mulOpt (Val 0) _          =   Val 0
> mulOpt x (Val 1)          =   optExpr False x
> mulOpt (Val 1) x          =   optExpr False x
> mulOpt (Val x) (Val y)    =   if (x == y) then Val (x^2) else Val (x * y)
> mulOpt x y                =   App Mul (optExpr False x) (optExpr False y)

> divOpt                    ::  Expr -> Expr -> Expr
> divOpt x (Val 1)          =   optExpr False x
> divOpt (Val 0) x          =   Val 0
> divOpt (Val x) (Val y)    =   Val (x `div` y)
> divOpt x y                =   if (x == y) then Val 1 else App Div (optExpr False x) (optExpr False y)


> compProg     ::  Prog -> WriterT Code (State Label) ()
> compProg pr  =   
>   case pr of
>       Assign v e  ->  do
>                           tell (compExpr e)
>                           tell [POP v]
>                           return ()
>       If e a b    ->  compIf e a b
>       While e pr  ->  compWhile e pr
>       Seqn prs    ->  compSeqn prs

> compIf       ::  Expr -> Prog -> Prog -> WriterT Code (State Label) ()
> compIf e a b =   do
>                       l   <-  get
>                       modify (+1)
>                       l'  <-  get
>                       modify (+1)
>                       tell (compExpr e)
>                       tell [JUMPZ l]
>                       true <- compProg a
>                       tell [JUMP l', LABEL l]
>                       false <- compProg b
>                       tell [LABEL l']
>                       return ()


> compWhile         ::  Expr -> Prog -> WriterT Code (State Label) ()
> compWhile e pr    =   do
>                           l   <-  get
>                           modify (+1)
>                           l'  <-  get
>                           modify (+1)
>                           tell [LABEL l]
>                           tell (compExpr e)
>                           tell [JUMPZ l']
>                           pr'  <-  compProg pr
>                           tell [JUMP l, LABEL l']
>                           return ()

> compSeqn          ::  [Prog] -> WriterT Code (State Label) ()
> compSeqn [pr]     =   compProg pr
> compSeqn (pr:prs) = do
>                       compFirst <- compProg pr
>                       compRest  <- compSeqn prs
>                       return ()

> comp      ::  Prog -> Code
> comp pr   =   snd $ fst $ runState (runWriterT $ compProg pr) 0



-----------------------------------------------------------------------
not monadic (but it probably shouldn't be anyway)

TODO:


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

> type Machine' = StateT Counter (StateT Mem (StateT Stack (Reader Code))) ()

> liftToMem     =   lift
> liftToStack   =   lift . lift

> getMem        =   liftToMem $ get
> getStack      =   liftToStack $ get

> modifyMem fn     =   liftToMem $ modify fn
> modifyStack fn   =   liftToStack $ modify fn

> incPC    =   modify (+1)

Writing as if it's imperative huehuehuehuehue

> execStep'     ::      Machine'
> execStep'     = do
>                   pc <- get
>                   c <- ask
>                   case (c !! pc) of
>                       PUSH n  ->  do
>                                       modifyStack (n:)
>                                       incPC
>                                       return ()
>                       PUSHV v ->  do
>                                       mem <- getMem
>                                       modifyStack ((loadVar v mem):)
>                                       incPC
>                                       return ()
>                       POP v   ->  do
>                                       st <- getStack
>                                       modifyMem (storeVar v (head st))
>                                       modifyStack tail
>                                       incPC
>                                       return ()
>                       DO op   ->  do
>                                       modifyStack (doOp op)
>                                       incPC
>                                       return ()
>                       LABEL l ->  do
>                                       incPC
>                                       return ()
>                       JUMP l  ->  do
>                                       put (findLabel l c)
>                                       return ()
>                       JUMPZ l ->  do
>                                       st <- getStack
>                                       if (head st) == 0 then
>                                           put (findLabel l c)
>                                       else
>                                           incPC
>                                       modifyStack tail
>                                       return ()

> execLoop'         ::      Machine'
> execLoop'         =   do
>                           pc <- get
>                           c  <- ask
>                           if pc >= (length c) then
>                               return ()
>                           else
>                               do
>                                   execStep'
>                                   execLoop'
>                               

> debug              ::  Code -> Stack -> Mem -> (Counter, Mem, Stack)
> debug c s m     =   (pc, mem, st)
>                       where
>                           (r, st) = runReader (runStateT (runStateT (runStateT execStep' 0) m) s) c
>                           (r', mem) = r
>                           (r'', pc) = r'

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

> exec'     ::  Code -> Mem
> exec' c   =  reverse $ remDupes $ mem
>                where
>                    (((_,_),mem),_) = runReader (runStateT (runStateT (runStateT execLoop' 0) []) []) c

--------------------------------------------------------------------------

 readCode          ::  String  ->  IO [Inst]
 readCode  file    =   


