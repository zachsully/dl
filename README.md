# A Dual Language
---

For now this just means `data` and `codata`.

```
codata NegPair a b
  { Fst : NegPair a b -> a
  , Snd : NegPair a b -> b }

Fst (Snd (cocase { Fst # -> 1
                 , Fst (Snd #) -> 2
                 , Snd # -> 3       }))
```
