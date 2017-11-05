data NegPair a b = MkNegPair { _Fst:: a , _Snd :: b }
  deriving Show

set_Fst :: NegPair a b -> a -> NegPair a b
set_Fst d x = MkNegPair x (_Snd d)

set_Snd :: NegPair a b -> b -> NegPair a b
set_Snd d y = MkNegPair (_Fst d) y

foo = set_Snd (set_Fst (error "unmatched copattern") 42) 0
bar = _Fst foo
