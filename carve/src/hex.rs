//! Numbers in the manifest are hex strings, matching the disassembly
//! (`[rcx+0x58]`), and stay exact for consumers that read JSON numbers as f64.

use serde::{Serialize, Serializer};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Hex(pub u64);

impl Serialize for Hex {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&format!("{:#x}", self.0))
    }
}

impl From<u64> for Hex {
    fn from(value: u64) -> Self {
        Self(value)
    }
}

impl From<u32> for Hex {
    fn from(value: u32) -> Self {
        Self(value.into())
    }
}

impl From<usize> for Hex {
    fn from(value: usize) -> Self {
        Self(value as u64)
    }
}

pub fn bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
