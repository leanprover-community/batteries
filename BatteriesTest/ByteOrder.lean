
module
meta import Batteries.Data.ByteOrder

#guard UInt16.byteswap 0x0102 == 0x0201
#guard UInt32.byteswap 0x01020304 == 0x04030201
#guard UInt64.byteswap 0x0102030405060708 == 0x0807060504030201

/- Tests for big endian platforms -/

#guard System.Platform.byteOrder != .bigEndian ||
  UInt16.toByteArray 0x0102 == .mk #[1, 2]
#guard System.Platform.byteOrder != .bigEndian ||
  UInt32.toByteArray 0x01020304 == .mk #[1, 2, 3, 4]
#guard System.Platform.byteOrder != .bigEndian ||
  UInt64.toByteArray 0x0102030405060708 == .mk #[1, 2, 3, 4, 5, 6, 7, 8]

#guard System.Platform.byteOrder != .bigEndian ||
  UInt16.ofByteArray (.mk #[1, 2]) rfl == 0x0102
#guard System.Platform.byteOrder != .bigEndian ||
  UInt32.ofByteArray (.mk #[1, 2, 3, 4]) rfl = 0x01020304
#guard System.Platform.byteOrder != .bigEndian ||
  UInt64.ofByteArray (.mk #[1, 2, 3, 4, 5, 6, 7, 8]) rfl == 0x0102030405060708

/- Tests for little endian platforms -/

#guard System.Platform.byteOrder != .littleEndian ||
  UInt16.toByteArray 0x0102 == .mk #[2, 1]
#guard System.Platform.byteOrder != .littleEndian ||
  UInt32.toByteArray 0x01020304 == .mk #[4, 3, 2, 1]
#guard System.Platform.byteOrder != .littleEndian ||
  UInt64.toByteArray 0x0102030405060708 == .mk #[8, 7, 6, 5, 4, 3, 2, 1]

#guard System.Platform.byteOrder != .littleEndian ||
  UInt16.ofByteArray (.mk #[2, 1]) rfl == 0x0102
#guard System.Platform.byteOrder != .littleEndian ||
  UInt32.ofByteArray (.mk #[4, 3, 2, 1]) rfl = 0x01020304
#guard System.Platform.byteOrder != .littleEndian ||
  UInt64.ofByteArray (.mk #[8, 7, 6, 5, 4, 3, 2, 1]) rfl == 0x0102030405060708
