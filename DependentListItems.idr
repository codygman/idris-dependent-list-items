data Composition : (a -> a -> Type) -> a -> a -> Type where
  Composition.Nil : Composition r x x
  Composition.(::) : r x y -> Composition r y z -> Composition r x z

data Ty = Key | FilePath | FileContents | NoInput

data Plugin : (inp, outp : Ty) -> Type where
  MkPlugin : (inp, outp : Ty) -> Plugin inp outp

-- First plugin takes no input and provides a Key, this is allowed because the second plugin takes a Key
-- try changing the second plugin to FilePath from Key and you'll get a type error like:
{-
- + Errors (1)
 `-- DependentListItems.idr line 16 col 21:
     When checking right hand side of plugins with expected type
             Composition Plugin NoInput FileContents

     When checking argument inp to constructor Main.MkPlugin:
             Type mismatch between
                     Key (Inferred value)
             and
                     FilePath (Given value)
-}
plugins : (Composition Plugin NoInput FileContents)
plugins = [ MkPlugin NoInput Key
          , MkPlugin Key FileContents
          ]


-- relevant discussion where #idris helped me figure the above out
  -- [10:40] <NicePerson> codygman: A composition list aka reflexive-transitive closure.
  -- [10:43] <NicePerson> codygman: Wait, I assume you meant Plugin : Type -> Type -> Type, because otherwise talking of input vs. output types makes no sense.

-- [16:25] <NicePerson> > :let data Composition : (a -> a -> Type) -> a -> a -> Type where Composition.Nil : Composition r x x; Composition.(::) : r x y -> Composition r y z -> Composition r x z
-- [16:25] <idris-bot> defined
-- [16:25] <NicePerson> > the (Composition (\a, b => a -> b) (List Integer) String) [map fromInteger, map (+ 0.5), reverse, show]
-- [16:25] <idris-bot> [\meth => Prelude.List.List implementation of Prelude.Functor.Functor, method map (\meth => prim__toFloatBigInt meth) meth,
-- [16:25] <idris-bot>  \meth => Prelude.List.List implementation of Prelude.Functor.Functor, method map (\ARG => prim__addFloat ARG 0.5) meth,
-- [16:25] <idris-bot>  Prelude.List.reverse, reverse' Double [],
-- [16:25] <idris-bot>  \meth =>
-- [16:25] <idris-bot>    prim__concat "["
-- [16:25] <idris-bot>                 (prim__concat (Prelude.Show.Prelude.Show.List a implementation of Prelude.Show.Show, method show, show' Double
-- [16:25] <idris-bot>                                                                                                                         meth
-- [16:25] <idris-bot>                                                                                                                         (constructor of Prelude.Show.Show (\meth => prim__floatToStr meth)
-- [16:25] <idris-bot>                                                                                                                                                           (\meth, meth =>
-- [16:25] <idris-bot>                                                                                                                                                              showParens (with block in Prelude.Interfaces.Prelude.Show.Prec implementation of Prelude.Interfaces.Ord, method > (Prelude.Show.Prec implementation of Prelude.Interfaces.Ord, method compare meth↵…
-- [16:26] <NicePerson> For something that’s less useful but more decent to look at:
  -- [16:28] <NicePerson> > with Composition [(6, True), (False, Z), (S Z, "foo")]
  -- [16:28] <idris-bot> Can't disambiguate name: Effects.Z, Prelude.Nat.Z
  -- [16:28] <NicePerson> > the (Composition Pair Integer String) [(6, True), (False, Nat.Z), (S Z, "foo")]
  -- [16:28] <idris-bot> [(6, True), (False, 0), (1, "foo")] : Composition Pair Integer String
  -- [16:29] <NicePerson> codygman: ↑ This is a list of pairs, where the snd of one pair and the fst of the next need to be the same type.
  -- [16:29] <NicePerson> > the (Composition Pair Integer String) [(6, True), (1.0, "foo")]
  -- [16:29] <idris-bot> (input):1:51-52:When checking argument a to constructor Builtins.MkPair:
  -- [16:29] <idris-bot>         Type mismatch between
  -- [16:29] <idris-bot>                 Double (Type of 1.0)
  -- [16:29] <idris-bot>         and
  -- [16:29] <idris-bot>                 Bool (Expected type)
  -- [16:30] <NicePerson> So that fails to typecheck because True and 1.0 are of different types.

  -- the (Composition Pair Integer String) [(6, True), (False, Nat.Z), (S Z, "foo")]

  -- data Composition : (a -> a -> Type) -> a -> a -> Type where Composition.Nil : Composition r x x; Composition.(::) : r x y -> Composition r y z -> Composition r x z
-- data Composition : (a -> a -> Type) -> a -> a -> Type where
--   Composition.Nil : Composition r x x
--   Composition.(::) : r x y -> Composition r y z -> Composition r x z

  -- [16:37] <NicePerson> codygman: So if you have a type Plugin : Type -> Type -> Type, and, for example, foo : Plugin String (Double, Double), and bar : Plugin (Double, Double) Action, you can put them into a composition, [foo, bar] : Composition Plugin String Action.

  -- [16:38] <NicePerson> codygman: Due to the polymorphism, it works just as well if your Plugin type takes arguments that are data-level representations of types.
  -- [16:40] <NicePerson> I mean that you might have to represent the types you can use as a datatype, often called a universe, because for example you need to pattern match on them.
  -- [16:41] <codygman> I might need to represent the types I use as a datatype so I can pattern match them as opposed to using ________ where you cannot pattern match on them.
  -- [16:42] <NicePerson> For example, if you build Plugin values at runtime whose input and output types are not statically known, you have to check at runtime that the types match to be able to put them into a Composition value.
  -- [16:42] <codygman> I think blank above is primitive types like int, string, etc. Is that correct
  -- [16:42] <NicePerson> No, I mean pattern-matching the types themselves.
  -- [16:42] <codygman> Okay
  -- [16:42] <NicePerson> You can’t go “case outputTy of Int => …; String => …”
  -- [16:43] <codygman> Right, that makes sense.
  -- [16:43] <NicePerson> So if you need to dispatch on types at runtime, like to check whether you can compose two plugins together, you need to represent them as data.
  -- [16:44] <NicePerson> Such as “data Ty = IntTy | StringTy | PairTy Ty Ty | …”
  -- [16:46] <NicePerson> And then your plugin type will be (Plugin : Ty -> Ty -> Type) so you can actually compare the type representations at runtime.
  -- [16:46] <NicePerson> > :t Composition
  -- [16:46] <idris-bot> Composition : (a -> a -> Type) -> a -> a -> Type
  -- [16:46] <NicePerson> And since Composition is polymorphic there it will work with that form as well.
  -- [16:53] <codygman> NicePerson: Oh. I see what you mean.
