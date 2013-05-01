
          ------------------------------------------
         |  G52AFP Coursework 2 - Monadic Compiler  |
         |                                          |
         |   Samuel Leask psysl1@nottingham.ac.uk   |
         |  Jonathan Sherry psyjs3@nottingham.ac.uk | 
          ------------------------------------------

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

--------------------------------------------------------------------------
Compilation

Compiles a given expression to code. Pattern matches on the type of expression after optimisation. 
In the case of 'App', recursively works on the operation's arguments to compile compound 
expressions and appends them together with a 'Do' and then the type of operation to execute 
the code above. 

> compExpr      :: Expr -> Code
> compExpr e =
>   case (optExpr True e) of
>       Val i                   ->  [PUSH i]
>       Var x                   ->  [PUSHV x]
>       App op a b              ->  (compExpr a) ++ (compExpr b) ++ [DO op]

Optimises expressions passed to it. Acts as a recursive skeleton with add/sub/mul/div Opt 
to make optimisations. The boolean passed around acts as primitive state. This function
filters out 'Val' and 'Var' expressions that cannot be optimised and feeds the arguments
of operation expressions into the relevant function to test if they can be optimised and
to perform the operation itself. 

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

Deals with addition operations. Makes common optimisations such as reducing x + 0 to x
or multiplying a value by two if arguments are the same. Also acts as the mechanism for 
addition of 'Val' expressions and deals with compound addition expressions.

> addOpt                    ::  Expr -> Expr -> Expr
> addOpt (Val 0) x          =   optExpr False x
> addOpt x (Val 0)          =   optExpr False x
> addOpt (Val x) (Val y)    =   Val (x + y)
> addOpt x y                =   if (x == y) then App Mul (Val 2) (optExpr False x) else App Add (optExpr False x) (optExpr False y)

Deals with subtraction operations, again making common optimisations such as reducing
x - 0 to x. Acts as the mechanism for 'Val' subtraction and deals with compund subtraction
expressions.

> subOpt                    ::  Expr -> Expr -> Expr
> subOpt x (Val 0)          =   optExpr False x
> subOpt (Val x) (Val y)    =   Val (x - y)
> subOpt x y                =   if (x == y) then Val 0 else App Sub (optExpr False x) (optExpr False y)

Deals with multiplication expressions. More optimisations can be made here to deal with
when 0 and 1 occur as arguments (i.e. x * 1 = x, x * 0 = 0 etc.). Similarly, squares
the first argument when both arguments are the same. Once more, acts as the mechanism
for 'Val' multiplication and deals with compound expressions.

> mulOpt                    ::  Expr -> Expr -> Expr
> mulOpt _ (Val 0)          =   Val 0
> mulOpt (Val 0) _          =   Val 0
> mulOpt x (Val 1)          =   optExpr False x
> mulOpt (Val 1) x          =   optExpr False x
> mulOpt (Val x) (Val y)    =   if (x == y) then Val (x^2) else Val (x * y)
> mulOpt x y                =   App Mul (optExpr False x) (optExpr False y)

Deals with division expressions. Similarly deals with arguments of 0 and 1 and arguments
that are the same. Performs the division operation on 'Val' arguments. Deals with compund
division expressions.

> divOpt                    ::  Expr -> Expr -> Expr
> divOpt x (Val 1)          =   optExpr False x
> divOpt (Val 0) x          =   Val 0
> divOpt (Val x) (Val y)    =   Val (x `div` y)
> divOpt x y                =   if (x == y) then Val 1 else App Div (optExpr False x) (optExpr False y)


Compiles a program. Uses the writer monad to construct the code. Pattern matches on the 
program passed to it. Explicitly deals with Assign statements by compiling the expression
to be assigned and adding it to the code being constructed, followed by a POP instruction.
Matches on other statements and passes them to relevant functions to be compiled.

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

Compiles If statements. First, uses the state monad to get labels. Compiles the conditional 
expression with compExpr then adds the conditional jump with a label fetched with get to the
and incremented with modify. It then calls compProg to compile the expression to be executed
if the result is true. JUMP and LABEL instructions are then added for the mechanism of the If
statement to work and then the expression to be executed if the conditional is false is 
compiled. Finally another Label instruction is added.

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

Compiles while statements. Works in a very similar way to compIf. Again, fetches labels 
with the state monad's get function. After fetching the labels an initial LABEL instruction
is added to the code followed by the conditional expression. A conditional JUMPZ instruction
is then added. The program to be executed while the conditional expression is true is then
compiled and finally the JUMP instruction to the beginning of the loop is added, along
with the label to be jumped to when the conditional becomes false. 

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

Compiles a sequence of 'Prog' statements in the form of a list. Works recursively. If the list
contains one element it will compile that else will compile the head of the list with compProg
followed by the remainder of the list by calling itself. 

> compSeqn          ::  [Prog] -> WriterT Code (State Label) ()
> compSeqn [pr]     =   compProg pr
> compSeqn (pr:prs) = do
>                       compFirst <- compProg pr
>                       compRest  <- compSeqn prs
>                       return ()

Function to initialise the state and writer monads. Uses WriterT constructor and runState to 
get the initial state. 

> comp      ::  Prog -> Code
> comp pr   =   snd $ fst $ runState (runWriterT $ compProg pr) 0



-----------------------------------------------------------------------

> type Counter = Int
> type Machine = (Code, Stack, Mem, Counter)

Function used to search for value counterpart to a given name within memory. Uses isLegit
to unwrap the Maybe monad.

> loadVar          ::  Name -> Mem -> Int
> loadVar var mem  =   isLegit $ lookup var mem
>                           where
>                               isLegit (Just x)    = x
>                               isLegit Nothing     = error "var not found in memory!"

Stores a value in memory by cons-ing it to the beginning of memory in a Name-Value pair. 

> storeVar          ::  Name -> Int -> Mem -> Mem
> storeVar v n m    =   (v,n):m

Performs stackwise operations by pattern matching on the given operation, fetching the 
top two elements from the stack, performing the operation and finally cons-ing the result
back on top of the stack.

> doOp              ::  Op -> Stack -> Stack
> doOp op (y:x:st)  =
>   case op of
>       Add         ->  (x + y):st
>       Sub         ->  (x - y):st
>       Mul         ->  (x * y):st
>       Div         ->  (x `div` y):st

Finds the counter associated with a given label. Matches on the result of the result of
findIndex, which returns the first element that has the same label as that provided. 

> findLabel         ::  Label -> Code -> Counter
> findLabel l c     =   case (findIndex pred c) of
>                           Just x      ->   x
>                           Nothing     ->   error "something has gone badly wrong!"
>                       where
>                           pred (LABEL l') = l' == l
>                           pred _          = False

Removes duplicate elements in memory using nubBy with a condition appropriate to the 
structure of memory.

> remDupes  ::  Mem -> Mem
> remDupes  =   nubBy (\(v, n) (v', n') -> v == v')

Main execution loop. Works recursively. If the program counter is ahead of, or at the 
end of the code then it will return the memory within the machine provided else it 
will call itself having executed a single step. In this way, execution occurs until 
the program counter reaches teh end of the code. 

> execLoop      ::  Machine -> Mem
> execLoop m    =   if (pc >= (length c)) then mem
>                       else
>                           execLoop (execStep m)
>                               where (c,_,mem,pc) = m

Executes a single step. Matches on the element of the code where the program counter
currently indicates and performs operations appropriate to the instruction. In the 
case of a PUSH instruction, the number carried is placed on top of the stack. A 
PUSHV instruction places a variable on the stack with loadVar. POP removes the top
element from the stack and places it in memory. Nothing is executed when encountering
a LABEL instruction. JUMP instructions move the program counter to the correct index
of the label using findLabel. JUMPZ acts like JUMP based on the truth of the top of 
the stack. After all instructions, bar JUMP and JUMPZ, the program counter is incremented.

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

--------------------------------------------------------------------------

Execution

Main execution function. Initialises a machine with an empty stack and memory, a
program counter at 0 and with the code provided. This is passed to execLoop to be
executed. Duplicates are then removed and it is reversed to yield the result of the
code in memory.

> exec	    ::	Code -> Mem
> exec c    =   reverse $ remDupes $ execLoop (c,[],[],0)

--------------------------------------------------------------------------

Debugging functions.

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
>   

--------------------------------------------------------------------------
