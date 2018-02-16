{-# LANGUAGE GADTs #-}

data MkNegPair a b
  = MkNegPair
  { _Fst :: a
  , _Snd :: b
  } deriving Show

main = print $
  let set_Fst = (\d ->
        (\x ->
              MkNegPair (x) (_Snd (d))))
  in let set_Snd = (\d ->
          (\x ->
                MkNegPair (_Fst (d)) (x)))
    in _Fst (set_Fst (set_Snd ((error "match fail")) (0)) (42))