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
(constraint (= (f #xAEF10DA66F8990AB) #x0000510EF2599076))
(constraint (= (f #x53E0633776150FB3) #x0000AC1F9CC889EA))
(constraint (= (f #x361E8C52603F7DCD) #x0000C9E173AD9FC0))
(constraint (= (f #x641CFB0EF73D84F3) #x00009BE304F108C2))
(constraint (= (f #x932840D6D8625DCF) #x00006CD7BF29279D))
(constraint (= (f #x000000000001ABCD) #x0000FFFFFFFFFFFF))
(constraint (= (f #x000000000001300D) #x0000FFFFFFFFFFFF))
(constraint (= (f #x0000000000017FBD) #x0000FFFFFFFFFFFF))
(constraint (= (f #x000000000001B143) #x0000FFFFFFFFFFFF))
(constraint (= (f #x000000000001E5D5) #x0000FFFFFFFFFFFF))
(constraint (= (f #x0C0E0D0614921C3D) #x0000F3F1F2F9EB6D))
(constraint (= (f #x680701E186061A13) #x000097F8FE1E79F9))
(constraint (= (f #x2485001685A0781D) #x0000DB7AFFE97A5F))
(constraint (= (f #xC2C1A1806003C0B5) #x00003D3E5E7F9FFC))
(constraint (= (f #x3052D05A0402D035) #x0000CFAD2FA5FBFD))
(constraint (= (f #x000000000001003D) #x0000FFFFFFFFFFFF))
(constraint (= (f #x0000000000018497) #x0000FFFFFFFFFFFF))
(constraint (= (f #x0000000000010E1F) #x0000FFFFFFFFFFFF))
(constraint (= (f #x0000000000016835) #x0000FFFFFFFFFFFF))
(constraint (= (f #x000000000001E0B5) #x0000FFFFFFFFFFFF))
(constraint (= (f #x6510C2BF714C7EFE) #x0000000000000000))
(constraint (= (f #x15612137829B6104) #x0000000000000000))
(constraint (= (f #x5B86504E087266E6) #x0000000000000000))
(constraint (= (f #xABD58C2B944763CC) #x0000000000000000))
(constraint (= (f #x3823685124F96638) #x0000000000000000))
(constraint (= (f #x000000000001A15C) #x0000000000000000))
(constraint (= (f #x000000000001818C) #x0000000000000000))
(constraint (= (f #x000000000001C716) #x0000000000000000))
(constraint (= (f #x000000000001A244) #x0000000000000000))
(constraint (= (f #x00000000000118F4) #x0000000000000000))
(constraint (= (f #xED5EEE4004416702) #x0000000000000000))
(constraint (= (f #x59A7E2EE2A47D16E) #x0000000000000000))
(constraint (= (f #xA9616E3DAC571C3A) #x0000000000000000))
(constraint (= (f #x6AC6C6E143CE3BC5) #x00009539391EBC31))
(constraint (= (f #x6C6EB64DEDEEDCE2) #x0000000000000000))
(constraint (= (f #x8A25E96CD52E2EC5) #x000075DA16932AD1))
(constraint (= (f #x31E8D0A38A4E167E) #x0000000000000000))
(constraint (= (f #xE4272013C59595AC) #x0000000000000000))
(constraint (= (f #x38E5937596E06D47) #x0000C71A6C8A691F))
(constraint (= (f #x9EEEADB04D099EA8) #x0000000000000000))
(constraint (= (f #x000000000001EA47) #x0000FFFFFFFFFFFF))
(constraint (= (f #x000000000001E974) #x0000000000000000))
(constraint (= (f #x000000000001FFFF) #x0000FFFFFFFFFFFE))
(constraint (= (f #x0000000000018497) #x0000FFFFFFFFFFFF))
(constraint (= (f #xA03041A0C1E14A1F) #x00005FCFBE5F3E1E))
(check-synth)
(define-fun f_1 ((x (BitVec 64))) (BitVec 64) (ite (= (bvlshr x #x0000000000000010) #x0000000000000001) (ite (= (bvor #x0000000000000001 x) x) (ite (= (bvor #x000000000000000e x) x) (ite (= (bvlshr x #x000000000000000f) #x0000000000000002) (bvlshr (bvnot #x0000000000000000) #x0000000000000010) (bvlshr (bvnot x) #x0000000000000010)) (bvlshr (bvnot #x0000000000000000) #x0000000000000010)) #x0000000000000000) (ite (= (bvor #x0000000000000001 x) x) (bvlshr (bvnot x) #x0000000000000010) #x0000000000000000)))
