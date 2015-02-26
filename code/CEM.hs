{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module CEM where

data Term n where
  Lam :: Term (S n) -> Term n
  Var :: Fin n -> Term n 
  App :: Term n -> Term n -> Term n

type ClosedTerm = Term Z

compileProgram :: ClosedTerm -> [BasicBlock]
data BasicBlock = BB Label [Instr]
type Label = String
type Instr = String

instance Eq BasicBlock where
  BB l _ == BB m _ = m == l
  
label :: Term n -> Label
label e = case e of
  Var i -> "v" ++ show (toInt i)
  Lam b -> "λ" ++ label b 
  App m n -> "d" ++ label m ++ "_" ++ label n ++ "b"

instance Show (Term n) where 
  show e = case e of
    Var i -> show $ toInt i
    Lam b -> "λ" ++ show b 
    App m n -> "(" ++ show m ++ " " ++ show n ++ ")"

compileProgram = compile

assembleData :: Term n -> [BasicBlock] 
assembleData e = let l = label e in case e of
  Var f -> []
  App m n -> assembleData m ++ assembleData n
  Lam b -> bb:assembleData b where
    bb = BB ("str" ++ l)
      [".ascii \"" ++ show e ++ "\\n\""
      ,"len" ++ l ++ " = . - " ++ "str" ++ l]

-- Need to remove duplicate labels, which ends up being a very simple common
-- subexpression elimination.
cse :: [BasicBlock] -> [BasicBlock]
cse bs = foldr replace [] bs where
  replace b@(BB l _) bs = if elem b bs then BB "" ["jmp "++l] : bs else b:bs

compile :: Term n -> [BasicBlock]
compile e = let l = label e in case e of
  Var i -> [varBB l i]
  Lam b -> BB l []
         : checkTermBB l
         : termBB l
         : checkUpdateBB l
         : updateBB l
         : takeBB l
         : compile b
  App m n -> appBB l (label n) : compile m ++ compile n

appBB :: Label -> Label -> BasicBlock
appBB l n = BB l
  ["push %rax"                                      -- Push environment
  ,"push $"++n]                                     -- Push argument code

varBB :: Label -> Fin n -> BasicBlock
varBB l i = BB l $
  replicate (toInt i) "movq 16(%rax), %rax"                 -- Index into environment
  ++ ["push %rax"                                   -- Push update location
     ,"push $0"                                     -- Push update marker
     ,"movq %rax, %rcx"                             -- \
     ,"movq 8(%rax), %rax"                          -- Load new Environment
     ,"jmp *(%rcx)"]                                -- Jump to new code

checkTermBB :: Label -> BasicBlock
checkTermBB l = BB ("CheckTerm_"++l)
  ["cmp %rsp, %rbp"                                 -- Check if stack is empty
  ,"jne CheckUpdate_"++ l]                      -- If not empty, check updates

termBB :: Label -> BasicBlock
termBB l = BB ("Term_"++ l)
  ["movq $str"++l++", %rsi"                            -- \
  ,"movq $len"++l++", %rdx"
  ,"movq $1, %rax"                                 -- Exit with label exitcode
  ,"syscall"
  ,"movq $0, %rdi"
  ,"movq $60, %rax"
  ,"syscall"]                                      -- / 

checkUpdateBB :: Label -> BasicBlock
checkUpdateBB l = BB ("CheckUpdate_"++ l)
  ["cmpq $0, (%rsp)"                                -- Check for update marker
  ,"jne Take_"++ l]                             -- If not update, proceed to take

updateBB :: Label -> BasicBlock
updateBB l = BB ("Update_"++ l)
  ["movq 8(%rsp), %rcx"                             -- \
  ,"movq $CheckTerm_"++ l ++", (%rcx)"       --  Replace code pointer
  ,"movq %rax, 8(%rcx)"                             --  Replace env pointer
  ,"add $16, %rsp"                                  --  Pop update 
  ,"jmp CheckTerm_"++ l]                        --  Continue with new stack
 
takeBB :: Label -> BasicBlock
takeBB l = BB ("Take_"++ l)
  ["pop (%rbx)"                                     -- Pop code into free heap cell
  ,"pop 8(%rbx)"                                    -- Pop env into free heap cell
  ,"movq %rax, 16(%rbx)"                            -- Point env to free heap cell
  ,"movq %rbx, %rax"                                -- /
  ,"add $24, %rbx"]                                 -- Increment free heap cell

data N = Z | S N
data Fin n where
  FZ :: Fin (S k)
  FS :: Fin k -> Fin (S k)

toInt :: Fin n -> Int
toInt FZ = 0
toInt (FS n) = 1 + toInt n
