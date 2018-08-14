import TaPL.SimplyTyped

main :: IO ()
main = testSimplyTyped

testSimplyTyped :: IO ()
testSimplyTyped = do
  let ctx1 = [("f", VarBind $ TyArrow TyBool TyBool)]
      t1   = TmApp (TmVar "f") (TmIf TmFalse TmTrue TmFalse)
  print $ eval ctx1 t1 