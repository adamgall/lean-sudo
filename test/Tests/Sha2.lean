import LeanSudo.Util.Sha2

/-! FIPS 180-4/NIST short and multi-block vectors. The additional repeated-byte
and padding-boundary vectors were independently computed with Python hashlib. -/
open LeanSudo.Sha2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

private def message0 := "".toUTF8
#guard hex (sha224 message0) == "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
#guard hex (sha256 message0) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hex (sha384 message0) == "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
#guard hex (sha512 message0) == "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"

private def message1 := "abc".toUTF8
#guard hex (sha224 message1) == "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
#guard hex (sha256 message1) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hex (sha384 message1) == "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
#guard hex (sha512 message1) == "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"

private def message2 := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8
#guard hex (sha224 message2) == "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525"
#guard hex (sha256 message2) == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard hex (sha384 message2) == "3391fdddfc8dc7393707a65b1b4709397cf8b1d162af05abfe8f450de5f36bc6b0455a8520bc4e6f5fe95b1fe3c8452b"
#guard hex (sha512 message2) == "204a8fc6dda82f0a0ced7beb8e08a41657c16ef468b228a8279be331a703c33596fd15c13b1b07f9aa1d3bea57789ca031ad85c7a71dd70354ec631238ca3445"

private def message3 := "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8
#guard hex (sha224 message3) == "c97ca9a559850ce97a04a96def6d99a9e0e0e2ab14e6b8df265fc0b3"
#guard hex (sha256 message3) == "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
#guard hex (sha384 message3) == "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039"
#guard hex (sha512 message3) == "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"

private def repeated55 : ByteArray := ⟨Array.replicate 55 97⟩
#guard hex (digest .sha224 repeated55) == "fb0bd626a70c28541dfa781bb5cc4d7d7f56622a58f01a0b1ddd646f"
#guard hex (digest .sha256 repeated55) == "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
#guard hex (digest .sha384 repeated55) == "5d91ac7e74e62b5c728904b40f10784d66b7af9cb6302123e48c92f0432ceb8d2a92c02de77dcb29ed75c4b42bde46f4"
#guard hex (digest .sha512 repeated55) == "b0220c772cbf6c1822e2cb38a437d0e1d58772417a4bbb21c961364f8b6143e05aa6316dca8d1d7b19e16448419076395f6086cb55101fbd6d5497b148e1745f"

private def repeated56 : ByteArray := ⟨Array.replicate 56 97⟩
#guard hex (digest .sha224 repeated56) == "d40854fc9caf172067136f2e29e1380b14626bf6f0dd06779f820dcd"
#guard hex (digest .sha256 repeated56) == "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
#guard hex (digest .sha384 repeated56) == "8a8d9649ea04e993a6ca7135af7e3392cc5fca84f8531cac7aa3feed4eb98f55dcbe0f3284b61c6f35f98b02cc644b4c"
#guard hex (digest .sha512 repeated56) == "962b64aae357d2a4fee3ded8b539bdc9d325081822b0bfc55583133aab44f18bafe11d72a7ae16c79ce2ba620ae2242d5144809161945f1367f41b3972e26e04"

private def repeated63 : ByteArray := ⟨Array.replicate 63 97⟩
#guard hex (digest .sha224 repeated63) == "1d4e051f4d6fed2a63fd2421e65834cec00d64456553de3496ae8b1d"
#guard hex (digest .sha256 repeated63) == "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"
#guard hex (digest .sha384 repeated63) == "7e7f097e95b52bb8f53383450ecaf9868187c130981730c03b6d573adfc0b991e365244e5b4bfa082bfb43c517d37120"
#guard hex (digest .sha512 repeated63) == "c1b0f5c6d3b03dfe4a2602e67242f54e344090b66e01100a469b129f583f016c7e27dddeaa438393dcc7ec54b0b57c9ba7af007f9b56db5f6fb677d972a31362"

private def repeated64 : ByteArray := ⟨Array.replicate 64 97⟩
#guard hex (digest .sha224 repeated64) == "a88cd5cde6d6fe9136a4e58b49167461ea95d388ca2bdb7afdc3cbf4"
#guard hex (digest .sha256 repeated64) == "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"
#guard hex (digest .sha384 repeated64) == "2e404b9339da795776e510d96930b3be2904c500395b8cb7413334b82d4dec413b4b8113045a05bbbcff846f027423f6"
#guard hex (digest .sha512 repeated64) == "01d35c10c6c38c2dcf48f7eebb3235fb5ad74a65ec4cd016e2354c637a8fb49b695ef3c1d6f7ae4cd74d78cc9c9bcac9d4f23a73019998a7f73038a5c9b2dbde"

private def repeated111 : ByteArray := ⟨Array.replicate 111 97⟩
#guard hex (digest .sha224 repeated111) == "4aeec1a49b2c1bc663abf2809b36faaa64359523d4f26d02dbc2cba3"
#guard hex (digest .sha256 repeated111) == "6374f73208854473827f6f6a3f43b1f53eaa3b82c21c1a6d69a2110b2a79baad"
#guard hex (digest .sha384 repeated111) == "3c37955051cb5c3026f94d551d5b5e2ac38d572ae4e07172085fed81f8466b8f90dc23a8ffcdea0b8d8e58e8fdacc80a"
#guard hex (digest .sha512 repeated111) == "fa9121c7b32b9e01733d034cfc78cbf67f926c7ed83e82200ef86818196921760b4beff48404df811b953828274461673c68d04e297b0eb7b2b4d60fc6b566a2"

private def repeated112 : ByteArray := ⟨Array.replicate 112 97⟩
#guard hex (digest .sha224 repeated112) == "0336b66821946e7f1052102e3b9c29f3039efe9b261746370305f894"
#guard hex (digest .sha256 repeated112) == "f54353008a2553262ecdc4a34749563ba0950e8b0fc8652780b0a614b99683c1"
#guard hex (digest .sha384 repeated112) == "187d4e07cb306103c69967bf544d0dfbe9042577599c73c330abc0cb64c61236d5ed565ee19119d8c31779a38f791fcd"
#guard hex (digest .sha512 repeated112) == "c01d080efd492776a1c43bd23dd99d0a2e626d481e16782e75d54c2503b5dc32bd05f0f1ba33e568b88fd2d970929b719ecbb152f58f130a407c8830604b70ca"

private def repeated127 : ByteArray := ⟨Array.replicate 127 97⟩
#guard hex (digest .sha224 repeated127) == "0822db3f33424aead078f71ed05f30edc077a3c254b7c79c89a7a4a1"
#guard hex (digest .sha256 repeated127) == "c57e9278af78fa3cab38667bef4ce29d783787a2f731d4e12200270f0c32320a"
#guard hex (digest .sha384 repeated127) == "9bd06b1763c2cf7aef40e795dc65bc96d59c41b537f3ad72ebdefd485476b5717c1aeb37c327fe9c1831b12b9efd08ae"
#guard hex (digest .sha512 repeated127) == "828613968b501dc00a97e08c73b118aa8876c26b8aac93df128502ab360f91bab50a51e088769a5c1eff4782ace147dce3642554199876374291f5d921629502"

private def repeated128 : ByteArray := ⟨Array.replicate 128 97⟩
#guard hex (digest .sha224 repeated128) == "39873a2441c56608137850f4c54dde157710b9a2b83c8bdc756dd643"
#guard hex (digest .sha256 repeated128) == "6836cf13bac400e9105071cd6af47084dfacad4e5e302c94bfed24e013afb73e"
#guard hex (digest .sha384 repeated128) == "edb12730a366098b3b2beac75a3bef1b0969b15c48e2163c23d96994f8d1bef760c7e27f3c464d3829f56c0d53808b0b"
#guard hex (digest .sha512 repeated128) == "b73d1929aa615934e61a871596b3f3b33359f42b8175602e89f7e06e5f658a243667807ed300314b95cacdd579f3e33abdfbe351909519a846d465c59582f321"

private def repeated1000 : ByteArray := ⟨Array.replicate 1000 97⟩
#guard hex (digest .sha224 repeated1000) == "4e8f0ce90b64661a2b5e84be6d93a7d9b76871062f1814433d04a03d"
#guard hex (digest .sha256 repeated1000) == "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
#guard hex (digest .sha384 repeated1000) == "f54480689c6b0b11d0303285d9a81b21a93bca6ba5a1b4472765dca4da45ee328082d469c650cd3b61b16d3266ab8ced"
#guard hex (digest .sha512 repeated1000) == "67ba5535a46e3f86dbfbed8cbbaf0125c76ed549ff8b0b9e03e0c88cf90fa634fa7b12b47d77b694de488ace8d9a65967dc96df599727d3292a8d9d447709c97"

-- NIST's million-'a' vectors exercise long inputs without constructing lists.
private def million : ByteArray := ⟨Array.replicate 1000000 97⟩
#guard hex (sha224 million) == "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67"
#guard hex (sha256 million) == "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
#guard hex (sha384 million) == "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985"
#guard hex (sha512 million) == "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b"
