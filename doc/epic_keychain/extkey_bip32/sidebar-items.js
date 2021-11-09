initSidebarItems({"enum":[["ChildNumber","A child number for a derived key"],["Error","A BIP32 error"]],"struct":[["BIP32GrinHasher","Implementation of the above that uses the standard BIP32 Hash algorithms"],["ChainCode","A chain code"],["ExtendedPrivKey","Extended private key"],["ExtendedPubKey","Extended public key"],["Fingerprint","A fingerprint"]],"trait":[["BIP32Hasher","Allow different implementations of hash functions used in BIP32 Derivations Epic uses blake2 everywhere but the spec calls for SHA512/Ripemd160, so allow this in future and allow us to unit test against published BIP32 test vectors The function names refer to the place of the hash in the reference BIP32 spec, not what the actual implementation is"]]});