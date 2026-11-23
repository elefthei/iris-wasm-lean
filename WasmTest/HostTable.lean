import IrisWasm.Host.IrisHost

namespace WasmTest.HostTable
open Wasm IrisWasm

private def initial : StoreRecord :=
  ⟨[.funcHost (.tf [] []) (.hostfuncidx 0)], [⟨RunTable.uniform 2 none, some 2⟩], [], []⟩

#guard (stabUpdate initial 0 2 0).isNone
#guard (stabUpdate initial 1 0 0).isNone
#guard (stabUpdate initial 0 1 0).any fun s =>
  s.tables[0]?.any fun t => t.entries.size == 2 && t.entries.get? 0 == some none &&
    t.entries.get? 1 == some (some 0) && t.maxOpt == some 2

end WasmTest.HostTable
