(Bottom, CAnd
  [ CSubset (Var "D") (FunApp "Null" [])
  , CSubset (Var "X") (Union (FunApp "Cons" [Top, Top]) (FunApp "Null" []))
  , CNot (CSubset (Var "X") (FunApp "Cons" [Top, Top]))
  , CImplies
      (CNot (CSubset (Intersect (FunApp "Null" []) (Var "X")) Bottom))
      (CAnd
         [ CSubset (Var "C1") (FunApp "Null" [])
         , CSubset (FunApp "Null" []) (Var "C1")
         ])
  , CImplies
      (CAnd
         [ CSubset (Intersect (FunApp "Null" []) (Var "X")) Bottom
         , CSubset Bottom (Intersect (FunApp "Null" []) (Var "X"))
         ])
      (CAnd [CSubset (Var "C1") Bottom, CSubset Bottom (Var "C1")])
  , CImplies
      (CNot
         (CSubset
            (Intersect (FunApp "Null" []) (FunApp "Cons" [Top, Top]))
            Bottom))
      (CAnd
         [ CSubset
             (Var "C2")
             (FunApp
                "Cons"
                [FunApp "Const" [], FunApp "Cons" [FunApp "Const" [], Var "D"]])
         , CSubset
             (FunApp
                "Cons"
                [FunApp "Const" [], FunApp "Cons" [FunApp "Const" [], Var "D"]])
             (Var "C2")
         ])
  , CImplies
      (CAnd
         [ CSubset
             (Intersect (FunApp "Null" []) (FunApp "Cons" [Top, Top]))
             Bottom
         , CSubset
             Bottom
             (Intersect (FunApp "Null" []) (FunApp "Cons" [Top, Top]))
         ])
      (CAnd [CSubset (Var "C2") Bottom, CSubset Bottom (Var "C2")])
  , CAnd
      [ CSubset (Var "D") (Union (Var "C1") (Var "C2"))
      , CSubset (Union (Var "C1") (Var "C2")) (Var "D")
      ]
  ])
