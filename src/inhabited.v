Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Global Hint Mode Inhabited ! : typeclass_instances.
Global Arguments populate {_} _ : assert.
