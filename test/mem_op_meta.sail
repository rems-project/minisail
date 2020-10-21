type mem_meta = int

union MemoryOpResult ('a : Type) = {
  MemValue     : 'a,
  MemException : int
}

/*
val MemoryOpResult_add_meta : forall ('t : Type). (MemoryOpResult('t), mem_meta) -> MemoryOpResult(('t, mem_meta))
function MemoryOpResult_add_meta(r, m) = match r {
  MemValue(v)     => MemValue(v, m),
  MemException(e) => MemException(e)
}
*/

val MemoryOpResult_add_meta : forall ('t : Type). (MemoryOpResult('t), mem_meta) -> MemoryOpResult('t)
function MemoryOpResult_add_meta(r, m) = match r {
  MemValue(v)     => MemValue(v)
}
