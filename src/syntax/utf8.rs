use std::io::{Result, Error, ErrorKind};
use std::convert::TryFrom;

fn get_next<I: Iterator<Item=Result<u8>>>(iter: &mut I) -> Result<u32> {
    match iter.next() {
        Some(Ok(c)) => {
            if c & 0xC0 == 0x80 {
                Ok((c & 0x3F) as u32)
            } else {
                Err(Error::new(ErrorKind::InvalidData, "invalid UTF-8 sequence."))
            }
        },
        Some(Err(e)) => Err(e),
        None => Err(Error::new(ErrorKind::UnexpectedEof, "unexpected end of UTF-8 sequence."))
    }
}

fn raw_decode_from<I: Iterator<Item=Result<u8>>>(a: u32, iter: &mut I) -> Result<u32> {
    if a & 0x80 == 0x00 {
        Ok(a)
    } else if a & 0xE0 == 0xC0 {
        let b = get_next(iter)?;
        Ok((a & 0x1F) << 6 | b)
    } else if a & 0xF0 == 0xE0 {
        let b = get_next(iter)?;
        let c = get_next(iter)?;
        Ok((a & 0x0F) << 12 | b << 6 | c)
    } else if a & 0xF8 == 0xF0 {
        let b = get_next(iter)?;
        let c = get_next(iter)?;
        let d = get_next(iter)?;
        Ok((a & 0x07) << 18 | b << 12 | c << 6 | d)
    } else {
        Err(Error::new(ErrorKind::InvalidData, "invalid UTF-8 sequence."))
    }
}

fn decode_from<I: Iterator<Item=Result<u8>>>(a: u32, iter: &mut I) -> Result<char> {
    match char::try_from(raw_decode_from(a, iter)?) {
        Ok(c) => Ok(c),
        Err(_) => Err(Error::new(ErrorKind::InvalidData, "invalid UTF-8 sequence."))
    }
}

pub fn decode<I: Iterator<Item=Result<u8>>>(iter: &mut I) -> Option<Result<char>> {
	match iter.next() {
		Some(Ok(a)) => Some(decode_from(a as u32, iter)),
		Some(Err(e)) => Some(Err(e)),
		None => None
	}
}
