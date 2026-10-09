"""Flags the Intel SDM (vol. 2, "Flags Affected") leaves undefined after an
instruction completes. The oracle prints them as `?` instead of the CPU's
value, and the model must leave exactly these flags `none`.

Letters: C carry, P parity, A auxiliary carry, Z zero, S sign, O overflow.
Instructions not listed define every flag they write.
"""

ALWAYS = {
    # "The OF and CF flags are cleared; the SF, ZF, and PF flags are set
    # according to the result. The state of the AF flag is undefined."
    "and": "A", "or": "A", "xor": "A", "test": "A",
    # "The SF, ZF, AF, and PF flags are undefined."
    "imul": "PAZS",
}


def shift(mnemonic, width, count):
    """SAL/SAR/SHL/SHR: "The CF flag contains the value of the last bit
    shifted out of the destination operand; it is undefined for SHL and SHR
    instructions where the count is greater than or equal to the size (in
    bits) of the destination operand. The OF flag is affected only for 1-bit
    shifts; otherwise, it is undefined. [...] If the count is 0, the flags are
    not affected. For a non-zero count, the AF flag is undefined."

    `count` is the count after the CPU masks it (to 6 bits for 64-bit
    operands, 5 otherwise)."""
    if count == 0:
        return ""
    flags = "A"
    if count != 1:
        flags += "O"
    if mnemonic in ("shl", "shr") and count >= width:
        flags += "C"
    return flags


def undefined(mnemonic, width=None, count=None):
    if mnemonic in ("shl", "shr", "sar"):
        return shift(mnemonic, width, count)
    return ALWAYS.get(mnemonic, "")
