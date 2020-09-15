(set-logic BV)
(synth-fun f ( (x (BitVec 64)) ) (BitVec 64)
((Start (BitVec 64)
((bvnot Start)
(bvxor Start Start)
(bvand Start Start)
(bvor Start Start)
(bvneg Start)
(bvadd Start Start)
(bvmul Start Start)
(bvudiv Start Start)
(bvurem Start Start)
(bvlshr Start Start)
(bvashr Start Start)
(bvshl Start Start)
(bvsdiv Start Start)
(bvsrem Start Start)
(bvsub Start Start)
x
#x0000000000000000
#x0000000000000001
#x0000000000000002
#x0000000000000003
#x0000000000000004
#x0000000000000005
#x0000000000000006
#x0000000000000007
#x0000000000000008
#x0000000000000009
#x0000000000000009
#x0000000000000009
#x000000000000000A
#x000000000000000B
#x000000000000000C
#x000000000000000D
#x000000000000000E
#x000000000000000F
#x0000000000000010
(ite StartBool Start Start)
))
(StartBool Bool
((= Start Start)
(not StartBool)
(and StartBool StartBool)
(or StartBool StartBool)
))))
(constraint (= (f #x159E0773A32AE0EC) #x00007FFFFFFFFFFF))
(constraint (= (f #xA5FD7B3C39ACD002) #x00007FFFFFFFFFFF))
(constraint (= (f #xDBC3BE617AD42AAC) #x00007FFFFFFFFFFF))
(constraint (= (f #xD6DF0F4B2DB478C6) #x00007FFFFFFFFFFF))
(constraint (= (f #x45F99FF2A2DC4800) #x00007FFFFFFFFFFF))
(constraint (= (f #x54FEC7D66D9E0CB9) #x00002B0138299261))
(constraint (= (f #x5AD868C88FFADE11) #x0000252797377005))
(constraint (= (f #x566E0EDFE8C668D3) #x00002991F1201739))
(constraint (= (f #x1039D39A258E5163) #x00006FC62C65DA71))
(constraint (= (f #x5D2BA590C1CEEF7A) #x000022D45A6F3E31))
(constraint (= (f #x6B448DE5EBD39F20) #x00007FFFFFFFFFFF))
(constraint (= (f #x478298E9B4411F28) #x00007FFFFFFFFFFF))
(constraint (= (f #x73D0943F8F6F8320) #x00007FFFFFFFFFFF))
(constraint (= (f #xED12611764E9C466) #x00007FFFFFFFFFFF))
(constraint (= (f #xAC45192F9AEF0022) #x00007FFFFFFFFFFF))
(constraint (= (f #xC9F0B849D3A574A3) #x0000360F47B62C5A))
(constraint (= (f #xD0B94F9572C18B58) #x00002F46B06A8D3E))
(constraint (= (f #x175B738E2567B227) #x000068A48C71DA98))
(constraint (= (f #xEE98DEB1F9A160AD) #x00001167214E065E))
(constraint (= (f #x557557CC446F7F51) #x00002A8AA833BB90))
(constraint (= (f #x20365EB5B54B1CF2) #x00005FC9A14A4AB4))
(constraint (= (f #x0B0DE8EF045CB8A6) #x00007FFFFFFFFFFF))
(constraint (= (f #x6C350E0493E7841A) #x000013CAF1FB6C18))
(constraint (= (f #x8946B4C842FC3388) #x00007FFFFFFFFFFF))
(constraint (= (f #x6C8697278E7E41B4) #x0000137968D87181))
(constraint (= (f #xFC4E6F14C61DA66D) #x000003B190EB39E2))
(constraint (= (f #xE91BB478C41B4709) #x000016E44B873BE4))
(constraint (= (f #xAEBA4DC331D049C2) #x00007FFFFFFFFFFF))
(constraint (= (f #x7A7EF26F00F1F97D) #x000005810D90FF0E))
(constraint (= (f #xDC149D52A6CC01C2) #x00007FFFFFFFFFFF))
(constraint (= (f #x6F30868934A90CCA) #x00007FFFFFFFFFFF))
(constraint (= (f #x2CC79849247D2CF6) #x0000533867B6DB82))
(constraint (= (f #x01AEEE953352C7E3) #x00007E51116ACCAD))
(check-synth)