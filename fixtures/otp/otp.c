#include <stdint.h>

extern void randombytes(uint8_t *buffer, uint64_t length);

/* The verified calling precondition restricts message to a byte. */
uint64_t encrypt_byte(uint64_t message, uint8_t *pad) {
    randombytes(pad, 1);
    return message ^ pad[0];
}
