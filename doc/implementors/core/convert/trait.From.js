(function() {var implementors = {};
implementors["epic_api"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'_ <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"epic_api/struct.QueryParams.html\" title=\"struct epic_api::QueryParams\">QueryParams</a>","synthetic":false,"types":["epic_api::web::QueryParams"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"https://doc.rust-lang.org/1.56.1/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;&amp;'_ <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.str.html\">str</a>&gt;&gt; for <a class=\"struct\" href=\"epic_api/struct.QueryParams.html\" title=\"struct epic_api::QueryParams\">QueryParams</a>","synthetic":false,"types":["epic_api::web::QueryParams"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://docs.rs/http/0.1.21/http/request/struct.Request.html\" title=\"struct http::request::Request\">Request</a>&lt;<a class=\"struct\" href=\"https://docs.rs/hyper/0.12.36/hyper/body/body/struct.Body.html\" title=\"struct hyper::body::body::Body\">Body</a>&gt;&gt; for <a class=\"struct\" href=\"epic_api/struct.QueryParams.html\" title=\"struct epic_api::QueryParams\">QueryParams</a>","synthetic":false,"types":["epic_api::web::QueryParams"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_api/enum.ErrorKind.html\" title=\"enum epic_api::ErrorKind\">ErrorKind</a>&gt; for <a class=\"struct\" href=\"epic_api/struct.Error.html\" title=\"struct epic_api::Error\">Error</a>","synthetic":false,"types":["epic_api::rest::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Context&lt;<a class=\"enum\" href=\"epic_api/enum.ErrorKind.html\" title=\"enum epic_api::ErrorKind\">ErrorKind</a>&gt;&gt; for <a class=\"struct\" href=\"epic_api/struct.Error.html\" title=\"struct epic_api::Error\">Error</a>","synthetic":false,"types":["epic_api::rest::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_api/enum.RouterError.html\" title=\"enum epic_api::RouterError\">RouterError</a>&gt; for <a class=\"struct\" href=\"epic_api/struct.Error.html\" title=\"struct epic_api::Error\">Error</a>","synthetic":false,"types":["epic_api::rest::Error"]}];
implementors["epic_chain"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_chain/enum.ErrorKind.html\" title=\"enum epic_chain::ErrorKind\">ErrorKind</a>&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Context&lt;<a class=\"enum\" href=\"epic_chain/enum.ErrorKind.html\" title=\"enum epic_chain::ErrorKind\">ErrorKind</a>&gt;&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_store/lmdb/enum.Error.html\" title=\"enum epic_store::lmdb::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/types/enum.Error.html\" title=\"enum epic_keychain::types::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/committed/enum.Error.html\" title=\"enum epic_core::core::committed::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"struct\" href=\"epic_chain/struct.Error.html\" title=\"struct epic_chain::Error\">Error</a>","synthetic":false,"types":["epic_chain::error::Error"]}];
implementors["epic_config"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_config/types/enum.ConfigError.html\" title=\"enum epic_config::types::ConfigError\">ConfigError</a>","synthetic":false,"types":["epic_config::types::ConfigError"]}];
implementors["epic_core"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/committed/enum.Error.html\" title=\"enum epic_core::core::committed::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>","synthetic":false,"types":["epic_core::core::block::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>","synthetic":false,"types":["epic_core::core::block::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/ser/enum.Error.html\" title=\"enum epic_core::ser::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>","synthetic":false,"types":["epic_core::core::block::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>","synthetic":false,"types":["epic_core::core::block::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/types/enum.Error.html\" title=\"enum epic_keychain::types::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>","synthetic":false,"types":["epic_core::core::block::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/core/block/struct.HeaderVersion.html\" title=\"struct epic_core::core::block::HeaderVersion\">HeaderVersion</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.u16.html\">u16</a>","synthetic":false,"types":[]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/core/block/struct.UntrustedBlockHeader.html\" title=\"struct epic_core::core::block::UntrustedBlockHeader\">UntrustedBlockHeader</a>&gt; for <a class=\"struct\" href=\"epic_core/core/block/struct.BlockHeader.html\" title=\"struct epic_core::core::block::BlockHeader\">BlockHeader</a>","synthetic":false,"types":["epic_core::core::block::BlockHeader"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/core/block/struct.UntrustedBlock.html\" title=\"struct epic_core::core::block::UntrustedBlock\">UntrustedBlock</a>&gt; for <a class=\"struct\" href=\"epic_core/core/block/struct.Block.html\" title=\"struct epic_core::core::block::Block\">Block</a>","synthetic":false,"types":["epic_core::core::block::Block"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"enum\" href=\"epic_core/core/committed/enum.Error.html\" title=\"enum epic_core::core::committed::Error\">Error</a>","synthetic":false,"types":["epic_core::core::committed::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/types/enum.Error.html\" title=\"enum epic_keychain::types::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/committed/enum.Error.html\" title=\"enum epic_core::core::committed::Error\">Error</a>","synthetic":false,"types":["epic_core::core::committed::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/core/block/struct.Block.html\" title=\"struct epic_core::core::block::Block\">Block</a>&gt; for <a class=\"struct\" href=\"epic_core/core/compact_block/struct.CompactBlock.html\" title=\"struct epic_core::core::compact_block::CompactBlock\">CompactBlock</a>","synthetic":false,"types":["epic_core::core::compact_block::CompactBlock"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/core/compact_block/struct.UntrustedCompactBlock.html\" title=\"struct epic_core::core::compact_block::UntrustedCompactBlock\">UntrustedCompactBlock</a>&gt; for <a class=\"struct\" href=\"epic_core/core/compact_block/struct.CompactBlock.html\" title=\"struct epic_core::core::compact_block::CompactBlock\">CompactBlock</a>","synthetic":false,"types":["epic_core::core::compact_block::CompactBlock"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/ser/enum.Error.html\" title=\"enum epic_core::ser::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>","synthetic":false,"types":["epic_core::core::transaction::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>","synthetic":false,"types":["epic_core::core::transaction::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/types/enum.Error.html\" title=\"enum epic_keychain::types::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>","synthetic":false,"types":["epic_core::core::transaction::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/committed/enum.Error.html\" title=\"enum epic_core::core::committed::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>","synthetic":false,"types":["epic_core::core::transaction::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/core/transaction/struct.Output.html\" title=\"struct epic_core::core::transaction::Output\">Output</a>&gt; for <a class=\"struct\" href=\"epic_core/core/transaction/struct.OutputIdentifier.html\" title=\"struct epic_core::core::transaction::OutputIdentifier\">OutputIdentifier</a>","synthetic":false,"types":["epic_core::core::transaction::OutputIdentifier"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/libtx/enum.ErrorKind.html\" title=\"enum epic_core::libtx::ErrorKind\">ErrorKind</a>&gt; for <a class=\"struct\" href=\"epic_core/libtx/struct.Error.html\" title=\"struct epic_core::libtx::Error\">Error</a>","synthetic":false,"types":["epic_core::libtx::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Context&lt;<a class=\"enum\" href=\"epic_core/libtx/enum.ErrorKind.html\" title=\"enum epic_core::libtx::ErrorKind\">ErrorKind</a>&gt;&gt; for <a class=\"struct\" href=\"epic_core/libtx/struct.Error.html\" title=\"struct epic_core::libtx::Error\">Error</a>","synthetic":false,"types":["epic_core::libtx::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"struct\" href=\"epic_core/libtx/struct.Error.html\" title=\"struct epic_core::libtx::Error\">Error</a>","synthetic":false,"types":["epic_core::libtx::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/types/enum.Error.html\" title=\"enum epic_keychain::types::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_core/libtx/struct.Error.html\" title=\"struct epic_core::libtx::Error\">Error</a>","synthetic":false,"types":["epic_core::libtx::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_core/libtx/struct.Error.html\" title=\"struct epic_core::libtx::Error\">Error</a>","synthetic":false,"types":["epic_core::libtx::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Context&lt;ErrorKind&gt;&gt; for <a class=\"struct\" href=\"epic_core/pow/struct.Error.html\" title=\"struct epic_core::pow::Error\">Error</a>","synthetic":false,"types":["epic_core::pow::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_core/pow/struct.Error.html\" title=\"struct epic_core::pow::Error\">Error</a>","synthetic":false,"types":["epic_core::pow::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"struct\" href=\"epic_core/pow/struct.Error.html\" title=\"struct epic_core::pow::Error\">Error</a>","synthetic":false,"types":["epic_core::pow::error::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'_ <a class=\"enum\" href=\"epic_core/pow/enum.Proof.html\" title=\"enum epic_core::pow::Proof\">Proof</a>&gt; for <a class=\"enum\" href=\"epic_core/core/block/feijoada/enum.PoWType.html\" title=\"enum epic_core::core::block::feijoada::PoWType\">PoWType</a>","synthetic":false,"types":["epic_core::pow::types::PoWType"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_core/ser/enum.Error.html\" title=\"enum epic_core::ser::Error\">Error</a>","synthetic":false,"types":["epic_core::ser::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/ser/struct.ProtocolVersion.html\" title=\"struct epic_core::ser::ProtocolVersion\">ProtocolVersion</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.u32.html\">u32</a>","synthetic":false,"types":[]}];
implementors["epic_keychain"] = [{"text":"impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.slice.html\">&amp;'a [</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.u8.html\">u8</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.slice.html\">]</a>&gt; for <a class=\"struct\" href=\"epic_keychain/extkey_bip32/struct.ChainCode.html\" title=\"struct epic_keychain::extkey_bip32::ChainCode\">ChainCode</a>","synthetic":false,"types":["epic_keychain::extkey_bip32::ChainCode"]},{"text":"impl&lt;'a&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.slice.html\">&amp;'a [</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.u8.html\">u8</a><a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.slice.html\">]</a>&gt; for <a class=\"struct\" href=\"epic_keychain/extkey_bip32/struct.Fingerprint.html\" title=\"struct epic_keychain::extkey_bip32::Fingerprint\">Fingerprint</a>","synthetic":false,"types":["epic_keychain::extkey_bip32::Fingerprint"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.u32.html\">u32</a>&gt; for <a class=\"enum\" href=\"epic_keychain/extkey_bip32/enum.ChildNumber.html\" title=\"enum epic_keychain::extkey_bip32::ChildNumber\">ChildNumber</a>","synthetic":false,"types":["epic_keychain::extkey_bip32::ChildNumber"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/extkey_bip32/enum.ChildNumber.html\" title=\"enum epic_keychain::extkey_bip32::ChildNumber\">ChildNumber</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.u32.html\">u32</a>","synthetic":false,"types":[]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"enum\" href=\"epic_keychain/extkey_bip32/enum.Error.html\" title=\"enum epic_keychain::extkey_bip32::Error\">Error</a>","synthetic":false,"types":["epic_keychain::extkey_bip32::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"enum\" href=\"epic_keychain/enum.Error.html\" title=\"enum epic_keychain::Error\">Error</a>","synthetic":false,"types":["epic_keychain::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/extkey_bip32/enum.Error.html\" title=\"enum epic_keychain::extkey_bip32::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_keychain/enum.Error.html\" title=\"enum epic_keychain::Error\">Error</a>","synthetic":false,"types":["epic_keychain::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'_ <a class=\"enum\" href=\"epic_keychain/enum.SwitchCommitmentType.html\" title=\"enum epic_keychain::SwitchCommitmentType\">SwitchCommitmentType</a>&gt; for <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.u8.html\">u8</a>","synthetic":false,"types":[]}];
implementors["epic_p2p"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/ser/enum.Error.html\" title=\"enum epic_core::ser::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_p2p/types/enum.Error.html\" title=\"enum epic_p2p::types::Error\">Error</a>","synthetic":false,"types":["epic_p2p::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_store/lmdb/enum.Error.html\" title=\"enum epic_store::lmdb::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_p2p/types/enum.Error.html\" title=\"enum epic_p2p::types::Error\">Error</a>","synthetic":false,"types":["epic_p2p::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_chain/error/struct.Error.html\" title=\"struct epic_chain::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_p2p/types/enum.Error.html\" title=\"enum epic_p2p::types::Error\">Error</a>","synthetic":false,"types":["epic_p2p::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_p2p/types/enum.Error.html\" title=\"enum epic_p2p::types::Error\">Error</a>","synthetic":false,"types":["epic_p2p::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_p2p/types/struct.PeerInfo.html\" title=\"struct epic_p2p::types::PeerInfo\">PeerInfo</a>&gt; for <a class=\"struct\" href=\"epic_p2p/types/struct.PeerInfoDisplay.html\" title=\"struct epic_p2p::types::PeerInfoDisplay\">PeerInfoDisplay</a>","synthetic":false,"types":["epic_p2p::types::PeerInfoDisplay"]}];
implementors["epic_pool"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/transaction/enum.Error.html\" title=\"enum epic_core::core::transaction::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_pool/types/enum.PoolError.html\" title=\"enum epic_pool::types::PoolError\">PoolError</a>","synthetic":false,"types":["epic_pool::types::PoolError"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_pool/types/enum.PoolError.html\" title=\"enum epic_pool::types::PoolError\">PoolError</a>","synthetic":false,"types":["epic_pool::types::PoolError"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/types/enum.Error.html\" title=\"enum epic_keychain::types::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_pool/types/enum.PoolError.html\" title=\"enum epic_pool::types::PoolError\">PoolError</a>","synthetic":false,"types":["epic_pool::types::PoolError"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/committed/enum.Error.html\" title=\"enum epic_core::core::committed::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_pool/types/enum.PoolError.html\" title=\"enum epic_pool::types::PoolError\">PoolError</a>","synthetic":false,"types":["epic_pool::types::PoolError"]}];
implementors["epic_servers"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_core/core/block/enum.Error.html\" title=\"enum epic_core::core::block::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_chain/error/struct.Error.html\" title=\"struct epic_chain::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/std/io/error/struct.Error.html\" title=\"struct std::io::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_p2p/types/enum.Error.html\" title=\"enum epic_p2p::types::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/pow/error/struct.Error.html\" title=\"struct epic_core::pow::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_store/lmdb/enum.Error.html\" title=\"enum epic_store::lmdb::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_api/rest/struct.Error.html\" title=\"struct epic_api::rest::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_pool/types/enum.PoolError.html\" title=\"enum epic_pool::types::PoolError\">PoolError</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"enum\" href=\"epic_keychain/types/enum.Error.html\" title=\"enum epic_keychain::types::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"epic_core/libtx/error/struct.Error.html\" title=\"struct epic_core::libtx::error::Error\">Error</a>&gt; for <a class=\"enum\" href=\"epic_servers/common/types/enum.Error.html\" title=\"enum epic_servers::common::types::Error\">Error</a>","synthetic":false,"types":["epic_servers::common::types::Error"]}];
implementors["epic_store"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;Error&gt; for <a class=\"enum\" href=\"epic_store/lmdb/enum.Error.html\" title=\"enum epic_store::lmdb::Error\">Error</a>","synthetic":false,"types":["epic_store::lmdb::Error"]}];
implementors["epic_util"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;&amp;'_ <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.56.1/std/primitive.str.html\">str</a>&gt; for <a class=\"struct\" href=\"epic_util/types/struct.ZeroingString.html\" title=\"struct epic_util::types::ZeroingString\">ZeroingString</a>","synthetic":false,"types":["epic_util::types::ZeroingString"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/1.56.1/core/convert/trait.From.html\" title=\"trait core::convert::From\">From</a>&lt;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.56.1/alloc/string/struct.String.html\" title=\"struct alloc::string::String\">String</a>&gt; for <a class=\"struct\" href=\"epic_util/types/struct.ZeroingString.html\" title=\"struct epic_util::types::ZeroingString\">ZeroingString</a>","synthetic":false,"types":["epic_util::types::ZeroingString"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()