/* Independent Microsoft deal generator for parity checks.
   The random number generator is Freecell Solver's own header (revision 5c057b7,
   copied unmodified in specs/references/fc-solve-5c057b7). The dealing loop follows
   that revision's range_solvers_gen_ms_boards.h; its offset table
   (board_gen_lookup1.h, not copied) places dealt card i in column i % 8, row i / 8.
   Output: "<game> <compact position>" lines, columns bottom to top, as `freecell deals`. */
#include <stdio.h>
#include "gen_ms_boards__rand.h"

static const char *values = "A23456789TJQK", *suits = "CDHS";

int main(int argc, char **argv) {
    unsigned long long from = strtoull(argv[1], NULL, 10), to = strtoull(argv[2], NULL, 10);
    for (unsigned long long deal = from; deal <= to; ++deal) {
        microsoft_rand seedx = microsoft_rand__calc_init_seedx((microsoft_rand)deal);
        size_t deck[52], cols[8][7], len[8] = {0};
        for (size_t i = 0; i < 52; ++i) deck[i] = i;
        microsoft_rand_uint left = 52;
        for (size_t i = 0; i < 52; ++i) {
            microsoft_rand_uint j = microsoft_rand__game_num_rand(&seedx, deal) % left;
            cols[i % 8][len[i % 8]++] = deck[j];
            deck[j] = deck[--left];
        }
        printf("%llu 0.0.0.0|", deal);
        for (int c = 0; c < 8; ++c) {
            printf("|");
            for (size_t r = 0; r < len[c]; ++r)
                printf("%s%c%c", r ? " " : "", values[cols[c][r] >> 2], suits[cols[c][r] & 3]);
        }
        printf("\n");
    }
    return 0;
}
