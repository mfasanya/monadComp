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

> compExpr	::	Expr -> Code
> compExpr e	=
>	case e of 
>		Val i 		    ->  [PUSH i]
>		Var x 		    ->  [PUSHV x]
>		App op e1 e2    ->  (compExpr e1) ++ (compExpr e2) ++ [DO op] 

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

> comp		::	Prog -> Code
> comp pr   =   fst $ compProg pr 0

Monadic, state is label

> data ST a     =   ST (Int -> (a, Int))
> instance Monad ST where
>   return x         =   ST $ \s -> (x,s)
>   (ST st) >>= f    =   ST $ \s -> let (x,s')  = st s
>                                       (ST q)  = f x 
>                                   in q s'

> label             ::  ST Int
> label             =   ST (\n -> (n, n+1))

> compIf'       :: Expr -> Prog -> Prog -> ST Code
> compIf' e t f = do
>                   l       <- label
>                   l'      <- label
>                   true    <- compProg' t
>                   false   <- compProg' f
>                   return ((compExpr e) ++ [JUMPZ l] ++ true ++ [JUMP l', LABEL l] ++ false ++ [LABEL l'])

> compWhile'        ::  Expr -> Prog -> ST Code
> compWhile' e pr   = do
>                       l   <- label
>                       l'  <- label
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



-----------------------------------------------------------------------
Execution
exec	::	Code -> Mem
