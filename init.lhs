G52AFP Coursework 2 - Monadic Compiler
   
Samuel Leask -psysl1@nottingham.ac.uk
Jonathan Sherry psyjs3@nottingham.ac.uk

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
comp		::	Prog -> Code

> compExpr	::	Expr -> Code
> compExpr e	=
>	case e of 
>		Val i 		-> [PUSH i]
>		Var x 		-> [PUSHV x]
>		App op e1 e2 -> [(compExpr e1),(compExpr e2), DO op]

--NOT Monadic		
compProg	::	Prog -> Label -> (Code, Label) 

--Monadic, state is label
compProg'	::	Prog -> ST Code





-----------------------------------------------------------------------
Execution
exec	::	Code -> Mem
