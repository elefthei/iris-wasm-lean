;; Diagnostic for WebAssembly/spec@6fca707686ed4f36a1e30ec2ae7d3dd32b276704.
;; $evalglobals allocates gt unchanged (4.4:180); $instantiate retains that store (4.4:202-206).
;; $allocmodule appends a second global with a closed type (4.4:125). Store_ok checks both
;; global instances (7.1:209), but Globalinst_ok needs [] |- gt (7.1:180). Index 0 is free
;; in the first global's stored type. Reading the export only observes the second global.
(module (type $s (struct))
  (global (export "g") (ref null $s) (ref.null $s)))
(assert_return (get "g") (ref.null struct))
