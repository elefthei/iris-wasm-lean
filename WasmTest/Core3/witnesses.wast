(module
  (memory $left 1)
  (memory $right 1)
  (data (memory $left) (i32.const 3) "\80")
  (data (memory $right) (i32.const 3) "\7f")
  (func (export "signed") (result i32) (i32.load8_s $left (i32.const 3)))
  (func (export "unsigned") (result i32) (i32.load8_u $left (i32.const 3)))
  (func (export "other") (result i32) (i32.load8_u $right (i32.const 3))))
(assert_return (invoke "signed") (i32.const 0xffffff80))
(assert_return (invoke "unsigned") (i32.const 0x80))
(assert_return (invoke "other") (i32.const 0x7f))

(module
  (memory i64 1)
  (func (export "peek") (param i64) (result i32) (i32.load8_u (local.get 0)))
  (func (export "offset") (param i64) (result i32) (i32.load8_u offset=1 (local.get 0))))
(assert_return (invoke "peek" (i64.const 0)) (i32.const 0))
(assert_trap (invoke "peek" (i64.const 0x100000000)) "out of bounds memory access")
(assert_trap (invoke "offset" (i64.const -1)) "out of bounds memory access")

(module definition $wide
  (memory i64 65537)
  (data (i64.const 0x100000001) "\ab")
  (func (export "above4G") (result i32) (i32.load8_u (i64.const 0x100000001))))
(module instance $wide_instance $wide)
(assert_return (invoke $wide_instance "above4G") (i32.const 0xab))

(module
  (func $identity (param i32) (result i32) (local.get 0))
  (func (export "tail") (param i32) (result i32) (return_call $identity (local.get 0))))
(assert_return (invoke "tail" (i32.const 9)) (i32.const 9))

(module definition $counter
  (global $g (export "count") (mut i32) (i32.const 0))
  (func (export "set") (param i32) (global.set $g (local.get 0))))
(module instance $first $counter)
(module instance $second $counter)
(register "first" $first)
(invoke $first "set" (i32.const 12))
(assert_return (get $first "count") (i32.const 12))
(assert_return (get $second "count") (i32.const 0))
(module $alias
  (import "first" "count" (global $g (mut i32)))
  (func (export "read") (result i32) (global.get $g)))
(assert_return (invoke $alias "read") (i32.const 12))
(assert_trap
  (module
    (import "first" "count" (global $g (mut i32)))
    (func $fail (global.set $g (i32.const 73)) (unreachable))
    (start $fail))
  "unreachable")
(assert_return (get $first "count") (i32.const 73))
(assert_return (get $second "count") (i32.const 0))
