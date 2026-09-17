-- Hand-written. A duplicate `hax-lib` crate in the dependency graph makes hax emit
-- some references under a MANGLED crate name -- `hax_lib_1`, `hax_lib_2`, … -- with
-- the index assigned by dependency order. That means the index is not stable: moving
-- a dependency between `[dependencies]` and `[dev-dependencies]` shifts it. So this
-- file aliases BOTH `hax_lib_1.*` and `hax_lib_2.*` onto the real `hax_lib.*`; the
-- extraction uses one set at a time and the other is dead but harmless.
--
-- Every abbreviation here is an alias, not a definition: nothing is assumed, and the
-- file disappears once the duplicate-crate bug is fixed upstream.
import CoreModels
import Hax

namespace hax_lib_1.prop

abbrev «Prop» : Type := hax_lib.prop.Prop
abbrev «forall» := @hax_lib.prop.«forall»

namespace «Prop»
abbrev from_bool := hax_lib.prop.Prop.from_bool
abbrev and := @hax_lib.prop.Prop.and
namespace Insts
abbrev CoreConvertFromBool := hax_lib.prop.Prop.Insts.CoreConvertFromBool
end Insts
end «Prop»

end hax_lib_1.prop

-- hax also emits the mangled crate name UNDER the `hax_lib` prefix for some
-- instance arguments (e.g. `hax_lib.hax_lib_1.prop.Prop.Insts.CoreConvertFromBool`);
-- alias those forms too.
namespace hax_lib
namespace hax_lib_1.prop.Prop.Insts
abbrev CoreConvertFromBool := hax_lib.prop.Prop.Insts.CoreConvertFromBool
end hax_lib_1.prop.Prop.Insts
end hax_lib

-- Type conversions (Usize, I32, Bool)
namespace hax_lib.Usize.Insts.Hax_lib_2IntToInt
  abbrev to_int := hax_lib.Usize.Insts.Hax_libIntToInt.to_int
end hax_lib.Usize.Insts.Hax_lib_2IntToInt

namespace hax_lib.I32.Insts.Hax_lib_2IntToInt
  abbrev to_int := hax_lib.I32.Insts.Hax_libIntToInt.to_int
end hax_lib.I32.Insts.Hax_lib_2IntToInt

namespace hax_lib.Bool.Insts.Hax_lib_2PropToProp
  abbrev to_prop := hax_lib.Bool.Insts.Hax_libPropToProp.to_prop
end hax_lib.Bool.Insts.Hax_lib_2PropToProp

namespace hax_lib_2.prop

abbrev «Prop» : Type := hax_lib.prop.Prop
abbrev «forall» := @hax_lib.prop.«forall»

namespace «Prop»
abbrev from_bool := hax_lib.prop.Prop.from_bool
abbrev and := @hax_lib.prop.Prop.and
namespace Insts
abbrev CoreConvertFromBool := hax_lib.prop.Prop.Insts.CoreConvertFromBool
end Insts
end «Prop»

end hax_lib_2.prop

namespace hax_lib
namespace hax_lib_2.prop.Prop.Insts
abbrev CoreConvertFromBool := hax_lib.prop.Prop.Insts.CoreConvertFromBool
end hax_lib_2.prop.Prop.Insts
end hax_lib

-- Logical Implications
namespace hax_lib_2.prop
  abbrev implies := @hax_lib.prop.implies
end hax_lib_2.prop

-- Propositional Operations (BitAnd)
namespace hax_lib_2.prop.Prop.Insts.CoreOpsBitBitAndTProp
  abbrev bitand := @hax_lib.prop.Prop.Insts.CoreOpsBitBitAndTProp.bitand
end hax_lib_2.prop.Prop.Insts.CoreOpsBitBitAndTProp

namespace hax_lib.hax_lib_2.prop.Prop.Insts.CoreOpsBitBitAndTProp
  abbrev bitand := @hax_lib.prop.Prop.Insts.CoreOpsBitBitAndTProp.bitand
end hax_lib.hax_lib_2.prop.Prop.Insts.CoreOpsBitBitAndTProp

-- Integer Operations (Add, PartialOrd)
namespace hax_lib.hax_lib_2.int.Int.Insts
  namespace CoreOpsArithAddIntInt
    abbrev add := hax_lib.int.Int.Insts.CoreOpsArithAddIntInt.add
  end CoreOpsArithAddIntInt

  abbrev CoreCmpPartialOrdInt := hax_lib.int.Int.Insts.CoreCmpPartialOrdInt
end hax_lib.hax_lib_2.int.Int.Insts

-- The same set again under the `_1` index (see the header).
namespace hax_lib.Usize.Insts.Hax_lib_1IntToInt
  abbrev to_int := hax_lib.Usize.Insts.Hax_libIntToInt.to_int
end hax_lib.Usize.Insts.Hax_lib_1IntToInt

namespace hax_lib.I32.Insts.Hax_lib_1IntToInt
  abbrev to_int := hax_lib.I32.Insts.Hax_libIntToInt.to_int
end hax_lib.I32.Insts.Hax_lib_1IntToInt

namespace hax_lib.Bool.Insts.Hax_lib_1PropToProp
  abbrev to_prop := hax_lib.Bool.Insts.Hax_libPropToProp.to_prop
end hax_lib.Bool.Insts.Hax_lib_1PropToProp

-- Logical Implications
namespace hax_lib_1.prop
  abbrev implies := @hax_lib.prop.implies
end hax_lib_1.prop

-- Propositional Operations (BitAnd)
namespace hax_lib_1.prop.Prop.Insts.CoreOpsBitBitAndTProp
  abbrev bitand := @hax_lib.prop.Prop.Insts.CoreOpsBitBitAndTProp.bitand
end hax_lib_1.prop.Prop.Insts.CoreOpsBitBitAndTProp

namespace hax_lib.hax_lib_1.prop.Prop.Insts.CoreOpsBitBitAndTProp
  abbrev bitand := @hax_lib.prop.Prop.Insts.CoreOpsBitBitAndTProp.bitand
end hax_lib.hax_lib_1.prop.Prop.Insts.CoreOpsBitBitAndTProp

-- Integer Operations (Add, PartialOrd)
namespace hax_lib.hax_lib_1.int.Int.Insts
  namespace CoreOpsArithAddIntInt
    abbrev add := hax_lib.int.Int.Insts.CoreOpsArithAddIntInt.add
  end CoreOpsArithAddIntInt

  abbrev CoreCmpPartialOrdInt := hax_lib.int.Int.Insts.CoreCmpPartialOrdInt
end hax_lib.hax_lib_1.int.Int.Insts
