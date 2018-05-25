module Main

%default total

data PrimType
     = PInt
     | PChar
     | PVoid

showTy : PrimType -> String
showTy PInt = "int"
showTy PChar = "char"
showTy PVoid = "void"

data Literal : PrimType -> Type where
     LInt : Integer -> Literal PInt
     LChar : Char -> Literal PChar

showLiteral : Literal ty -> String
showLiteral (LInt x) = show x
showLiteral (LChar x) = singleton x

data Variable : Type -> PrimType -> Type where
     MkVariable : (label : t) -> Variable t p

showVariable : (label -> String) -> Variable label ty -> String
showVariable showLabel (MkVariable label) = "var_" ++ showLabel label

data Function : Type -> List PrimType -> PrimType -> Type where
     MkFunction : (label : t) -> Function t argTys retTy

showFunction : (label -> String) -> Function label tys ty -> String
showFunction showLabel (MkFunction label) = "function_" ++ showLabel label

data Argument : PrimType -> Type where
     MkArgument : (ty : PrimType) -> Variable label ty -> Argument ty

mutual 
  genFunType : Type -> List PrimType -> PrimType -> Type
  genFunType label [] retTy = AST label retTy ()
  genFunType label (ty::tys) retTy = Variable label ty -> genFunType label tys retTy

  data AST : Type -> PrimType -> Type -> Type where
      Lit : Literal p -> AST label p ()
      Add : AST label PInt () -> AST label PInt () -> AST label PInt ()
      Var : Variable label a -> AST label a ()
      Declare : (ty : PrimType) -> (Variable label ty -> AST label a ()) -> AST label a ()
      Assign : Variable label ty -> AST label ty () -> AST label ty ()
      AssignThen : Variable label ty -> AST label ty () -> AST label ty' () -> AST label ty' ()
      Define
         : (retTy : PrimType)
        -> (argTys : List PrimType)
        -> (Function label argTys retTy -> genFunType label argTys retTy)
        -> AST label PVoid ()
      Skip : AST label ty a
      Return : AST label ty () -> AST label ty ()

interface Primitive ty (ty' : PrimType) where
  coerce : ty -> AST label ty' ()

Primitive Integer PInt where
  coerce = Lit . LInt

term syntax int {name} ";" [rest] = Declare PInt (\name => rest)
term syntax [ty] {name} ";" [rest] = Declare ty (\name => rest)
term syntax int {name} "()" "{" [rest] "}" = Define PInt Nil (\name => rest)
term syntax [ty] {name} "()" "{" [rest] "}" = Define ty Nil (\name => rest)
term syntax [name] "=" [val] ";" [rest] = AssignThen name (coerce val) rest
term syntax "(" [name] "=" [val] ")" = Assign name (coerce val)
term syntax return [a] ";" = Return (coerce a)

namespace ArgList
  data ArgList : Type -> List PrimType -> Type where
    Nil : ArgList label []
    (::) : (var : Variable label t) -> ArgList label ts -> ArgList label (t::ts)

  showArgs : (label -> String) -> (tys : List PrimType) -> ArgList label tys -> String
  showArgs showLabel [] [] = ""
  showArgs showLabel [ty] [var] = showTy ty ++ " " ++ showVariable showLabel var
  showArgs showLabel (ty::tys) (var::vars) =
    showTy ty ++ " " ++ showVariable showLabel var ++ ", " ++ showArgs showLabel tys vars

  applyArgs
     : (argTys : List PrimType)
    -> Stream label
    -> (Function label argTys retTy -> genFunType label argTys retTy)
    -> ( Stream label
       , Function label argTys retTy
       , (as : List PrimType ** ArgList label as)
       , AST label retTy ()
       )
  applyArgs tys (funcName::labels) f =
    let func = MkFunction funcName
        (labels', hlist, ast) = go tys labels (f func)
    in (labels', func, hlist, ast)
    where
      go
        : (argTys : List PrimType)
        -> Stream label
        -> (genFunType label argTys retTy)
        -> ( Stream label
           , (as : List PrimType ** ArgList label as)
           , AST label retTy ()
           )
      go [] labels f = (labels, (_ ** Nil), f)
      go (ty::tys) (label::labels) f =
        let var = MkVariable label
            (labels', (_ ** hlist'), ast') = go tys labels (f var)
        in (labels', (_ ** var::hlist'), ast')

showAST : (label -> String) -> Stream label -> AST label ty a -> String
showAST showLabel labels Skip = ""
showAST showLabel labels (AssignThen a b rest) =
  showAST showLabel labels (assert_smaller (AssignThen a b rest) (Assign a b)) ++
  ";\n" ++ showAST showLabel labels rest
showAST showLabel labels (Return x) = "return " ++ showAST showLabel labels x ++ ";"
showAST showLabel labels (Lit x) = showLiteral x
showAST showLabel labels (Add x y) =
  unwords
  [ showAST showLabel labels x
  , "+"
  , showAST showLabel labels y
  ]
showAST showLabel labels (Var v) = showVariable showLabel v
showAST showLabel (label::labels) (Declare ty f) =
  let var = MkVariable label
  in unlines
  [ unwords [ showTy ty, showVariable showLabel var ] ++ ";"
  , showAST showLabel labels $ f var
  ]
showAST showLabel labels (Assign x y) =
  unwords
  [ showVariable showLabel x
  , "="
  , showAST showLabel labels y
  ]
showAST showLabel labels (Define retTy argTys f) =
  let (labels', f', (argTys' ** vars), ast) = applyArgs argTys labels f
  in unlines
     [ showTy retTy ++ " " ++
       showFunction showLabel f' ++
       "(" ++ showArgs showLabel argTys' vars ++ ") {"
     , showAST showLabel labels' (assert_smaller (Define retTy argTys f) ast)
     , "}"
     ]

infinity : Stream Int
infinity = iterate (+1) 0

showASTCounted : AST Int ty a -> String
showASTCounted = showAST show infinity

test1 : AST label PVoid ()
test1 = Define PInt [PInt] $ \func, a => Var a

test2 : AST label PVoid ()
test2 = Define PInt [PInt, PChar, PInt] $ \func, a, b, c => Add (Var a) (Var c)

test3 : AST label PVoid ()
test3 =
  int main() {
    int a;
    a = 2;
    return 0;
  }

main : IO ()
main = putStr $ showASTCounted test3
