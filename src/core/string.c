/*
* Copyright (c) 2019 Calvin Rose
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to
* deal in the Software without restriction, including without limitation the
* rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
* sell copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
* IN THE SOFTWARE.
*/

#include <ctype.h>
#include <string.h>

#ifndef JANET_AMALG
#include <janet.h>
#include "gc.h"
#include "util.h"
#include "state.h"
#endif

/* Begin building a string */
uint8_t *janet_string_begin(int32_t length) {
    JanetStringHead *head = janet_gcalloc(JANET_MEMORY_STRING, sizeof(JanetStringHead) + length + 1);
    head->length = length;
    uint8_t *data = (uint8_t *)head->data;
    data[length] = 0;
    return data;
}

/* Finish building a string */
const uint8_t *janet_string_end(uint8_t *str) {
    janet_string_hash(str) = janet_string_calchash(str, janet_string_length(str));
    return str;
}

/* Load a buffer as a string */
const uint8_t *janet_string(const uint8_t *buf, int32_t len) {
    JanetStringHead *head = janet_gcalloc(JANET_MEMORY_STRING, sizeof(JanetStringHead) + len + 1);
    head->length = len;
    head->hash = janet_string_calchash(buf, len);
    uint8_t *data = (uint8_t *)head->data;
    memcpy(data, buf, len);
    data[len] = 0;
    return data;
}

/* Compare two strings */
int janet_string_compare(const uint8_t *lhs, const uint8_t *rhs) {
    int32_t xlen = janet_string_length(lhs);
    int32_t ylen = janet_string_length(rhs);
    int32_t len = xlen > ylen ? ylen : xlen;
    int res = memcmp(lhs, rhs, len);
    if (res) return res;
    if (xlen == ylen) return 0;
    return xlen < ylen ? -1 : 1;
}

/* Compare a janet string with a piece of memory */
int janet_string_equalconst(const uint8_t *lhs, const uint8_t *rhs, int32_t rlen, int32_t rhash) {
    int32_t lhash = janet_string_hash(lhs);
    int32_t llen = janet_string_length(lhs);
    if (lhs == rhs)
        return 1;
    if (lhash != rhash || llen != rlen)
        return 0;
    return !memcmp(lhs, rhs, rlen);
}

/* Check if two strings are equal */
int janet_string_equal(const uint8_t *lhs, const uint8_t *rhs) {
    return janet_string_equalconst(lhs, rhs,
                                   janet_string_length(rhs), janet_string_hash(rhs));
}

/* Load a c string */
const uint8_t *janet_cstring(const char *str) {
    return janet_string((const uint8_t *)str, (int32_t)strlen(str));
}

/* Knuth Morris Pratt Algorithm */

struct kmp_state {
    int32_t i;
    int32_t j;
    int32_t textlen;
    int32_t patlen;
    int32_t *lookup;
    const uint8_t *text;
    const uint8_t *pat;
};

static void kmp_init(
    struct kmp_state *s,
    const uint8_t *text, int32_t textlen,
    const uint8_t *pat, int32_t patlen) {
    int32_t *lookup = calloc(patlen, sizeof(int32_t));
    if (!lookup) {
        JANET_OUT_OF_MEMORY;
    }
    s->lookup = lookup;
    s->i = 0;
    s->j = 0;
    s->text = text;
    s->pat = pat;
    s->textlen = textlen;
    s->patlen = patlen;
    /* Init state machine */
    {
        int32_t i, j;
        for (i = 1, j = 0; i < patlen; i++) {
            while (j && pat[j] != pat[i]) j = lookup[j - 1];
            if (pat[j] == pat[i]) j++;
            lookup[i] = j;
        }
    }
}

static void kmp_deinit(struct kmp_state *state) {
    free(state->lookup);
}

static void kmp_seti(struct kmp_state *state, int32_t i) {
    state->i = i;
    state->j = 0;
}

static int32_t kmp_next(struct kmp_state *state) {
    int32_t i = state->i;
    int32_t j = state->j;
    int32_t textlen = state->textlen;
    int32_t patlen = state->patlen;
    const uint8_t *text = state->text;
    const uint8_t *pat = state->pat;
    int32_t *lookup = state->lookup;
    while (i < textlen) {
        if (text[i] == pat[j]) {
            if (j == patlen - 1) {
                state->i = i + 1;
                state->j = lookup[j];
                return i - j;
            } else {
                i++;
                j++;
            }
        } else {
            if (j > 0) {
                j = lookup[j - 1];
            } else {
                i++;
            }
        }
    }
    return -1;
}

/* CFuns */

static Janet cfun_string_slice(int32_t argc, Janet *argv) {
    JanetRange range = janet_getslice(argc, argv);
    JanetByteView view = janet_getbytes(argv, 0);
    return janet_stringv(view.bytes + range.start, range.end - range.start);
}

static Janet cfun_string_repeat(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 2);
    JanetByteView view = janet_getbytes(argv, 0);
    int32_t rep = janet_getinteger(argv, 1);
    if (rep < 0) janet_panic("expected non-negative number of repetitions");
    if (rep == 0) return janet_cstringv("");
    int64_t mulres = (int64_t) rep * view.len;
    if (mulres > INT32_MAX) janet_panic("result string is too long");
    uint8_t *newbuf = janet_string_begin((int32_t) mulres);
    uint8_t *end = newbuf + mulres;
    for (uint8_t *p = newbuf; p < end; p += view.len) {
        memcpy(p, view.bytes, view.len);
    }
    return janet_wrap_string(janet_string_end(newbuf));
}

static Janet cfun_string_bytes(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    JanetByteView view = janet_getbytes(argv, 0);
    Janet *tup = janet_tuple_begin(view.len);
    int32_t i;
    for (i = 0; i < view.len; i++) {
        tup[i] = janet_wrap_integer((int32_t) view.bytes[i]);
    }
    return janet_wrap_tuple(janet_tuple_end(tup));
}

static Janet cfun_string_frombytes(int32_t argc, Janet *argv) {
    int32_t i;
    uint8_t *buf = janet_string_begin(argc);
    for (i = 0; i < argc; i++) {
        int32_t c = janet_getinteger(argv, i);
        buf[i] = c & 0xFF;
    }
    return janet_wrap_string(janet_string_end(buf));
}

static Janet cfun_string_asciilower(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    JanetByteView view = janet_getbytes(argv, 0);
    uint8_t *buf = janet_string_begin(view.len);
    for (int32_t i = 0; i < view.len; i++) {
        uint8_t c = view.bytes[i];
        if (c >= 65 && c <= 90) {
            buf[i] = c + 32;
        } else {
            buf[i] = c;
        }
    }
    return janet_wrap_string(janet_string_end(buf));
}

static Janet cfun_string_asciiupper(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    JanetByteView view = janet_getbytes(argv, 0);
    uint8_t *buf = janet_string_begin(view.len);
    for (int32_t i = 0; i < view.len; i++) {
        uint8_t c = view.bytes[i];
        if (c >= 97 && c <= 122) {
            buf[i] = c - 32;
        } else {
            buf[i] = c;
        }
    }
    return janet_wrap_string(janet_string_end(buf));
}

static Janet cfun_string_reverse(int32_t argc, Janet *argv) {
    janet_fixarity(argc, 1);
    JanetByteView view = janet_getbytes(argv, 0);
    uint8_t *buf = janet_string_begin(view.len);
    int32_t i, j;
    for (i = 0, j = view.len - 1; i < view.len; i++, j--) {
        buf[i] = view.bytes[j];
    }
    return janet_wrap_string(janet_string_end(buf));
}

static void findsetup(int32_t argc, Janet *argv, struct kmp_state *s, int32_t extra) {
    janet_arity(argc, 2, 3 + extra);
    JanetByteView pat = janet_getbytes(argv, 0);
    JanetByteView text = janet_getbytes(argv, 1);
    int32_t start = 0;
    if (argc >= 3) {
        start = janet_getinteger(argv, 2);
        if (start < 0) janet_panic("expected non-negative start index");
    }
    kmp_init(s, text.bytes, text.len, pat.bytes, pat.len);
    s->i = start;
}

static Janet cfun_string_find(int32_t argc, Janet *argv) {
    int32_t result;
    struct kmp_state state;
    findsetup(argc, argv, &state, 0);
    result = kmp_next(&state);
    kmp_deinit(&state);
    return result < 0
           ? janet_wrap_nil()
           : janet_wrap_integer(result);
}

static Janet cfun_string_findall(int32_t argc, Janet *argv) {
    int32_t result;
    struct kmp_state state;
    findsetup(argc, argv, &state, 0);
    JanetArray *array = janet_array(0);
    while ((result = kmp_next(&state)) >= 0) {
        janet_array_push(array, janet_wrap_integer(result));
    }
    kmp_deinit(&state);
    return janet_wrap_array(array);
}

struct replace_state {
    struct kmp_state kmp;
    const uint8_t *subst;
    int32_t substlen;
};

static void replacesetup(int32_t argc, Janet *argv, struct replace_state *s) {
    janet_arity(argc, 3, 4);
    JanetByteView pat = janet_getbytes(argv, 0);
    JanetByteView subst = janet_getbytes(argv, 1);
    JanetByteView text = janet_getbytes(argv, 2);
    int32_t start = 0;
    if (argc == 4) {
        start = janet_getinteger(argv, 3);
        if (start < 0) janet_panic("expected non-negative start index");
    }
    kmp_init(&s->kmp, text.bytes, text.len, pat.bytes, pat.len);
    s->kmp.i = start;
    s->subst = subst.bytes;
    s->substlen = subst.len;
}

static Janet cfun_string_replace(int32_t argc, Janet *argv) {
    int32_t result;
    struct replace_state s;
    uint8_t *buf;
    replacesetup(argc, argv, &s);
    result = kmp_next(&s.kmp);
    if (result < 0) {
        kmp_deinit(&s.kmp);
        return janet_stringv(s.kmp.text, s.kmp.textlen);
    }
    buf = janet_string_begin(s.kmp.textlen - s.kmp.patlen + s.substlen);
    memcpy(buf, s.kmp.text, result);
    memcpy(buf + result, s.subst, s.substlen);
    memcpy(buf + result + s.substlen,
           s.kmp.text + result + s.kmp.patlen,
           s.kmp.textlen - result - s.kmp.patlen);
    kmp_deinit(&s.kmp);
    return janet_wrap_string(janet_string_end(buf));
}

static Janet cfun_string_replaceall(int32_t argc, Janet *argv) {
    int32_t result;
    struct replace_state s;
    JanetBuffer b;
    int32_t lastindex = 0;
    replacesetup(argc, argv, &s);
    janet_buffer_init(&b, s.kmp.textlen);
    while ((result = kmp_next(&s.kmp)) >= 0) {
        janet_buffer_push_bytes(&b, s.kmp.text + lastindex, result - lastindex);
        janet_buffer_push_bytes(&b, s.subst, s.substlen);
        lastindex = result + s.kmp.patlen;
        kmp_seti(&s.kmp, lastindex);
    }
    janet_buffer_push_bytes(&b, s.kmp.text + lastindex, s.kmp.textlen - lastindex);
    const uint8_t *ret = janet_string(b.data, b.count);
    janet_buffer_deinit(&b);
    kmp_deinit(&s.kmp);
    return janet_wrap_string(ret);
}

static Janet cfun_string_split(int32_t argc, Janet *argv) {
    int32_t result;
    JanetArray *array;
    struct kmp_state state;
    int32_t limit = -1, lastindex = 0;
    if (argc == 4) {
        limit = janet_getinteger(argv, 3);
    }
    findsetup(argc, argv, &state, 1);
    array = janet_array(0);
    while ((result = kmp_next(&state)) >= 0 && limit--) {
        const uint8_t *slice = janet_string(state.text + lastindex, result - lastindex);
        janet_array_push(array, janet_wrap_string(slice));
        lastindex = result + state.patlen;
    }
    {
        const uint8_t *slice = janet_string(state.text + lastindex, state.textlen - lastindex);
        janet_array_push(array, janet_wrap_string(slice));
    }
    kmp_deinit(&state);
    return janet_wrap_array(array);
}

static Janet cfun_string_checkset(int32_t argc, Janet *argv) {
    uint32_t bitset[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    janet_arity(argc, 2, 3);
    JanetByteView set = janet_getbytes(argv, 0);
    JanetByteView str = janet_getbytes(argv, 1);
    /* Populate set */
    for (int32_t i = 0; i < set.len; i++) {
        int index = set.bytes[i] >> 5;
        uint32_t mask = 1 << (set.bytes[i] & 7);
        bitset[index] |= mask;
    }
    if (argc == 3) {
        if (janet_getboolean(argv, 2)) {
            for (int i = 0; i < 8; i++)
                bitset[i] = ~bitset[i];
        }
    }
    /* Check set */
    for (int32_t i = 0; i < str.len; i++) {
        int index = str.bytes[i] >> 5;
        uint32_t mask = 1 << (str.bytes[i] & 7);
        if (!(bitset[index] & mask)) {
            return janet_wrap_false();
        }
    }
    return janet_wrap_true();
}

static Janet cfun_string_join(int32_t argc, Janet *argv) {
    janet_arity(argc, 1, 2);
    JanetView parts = janet_getindexed(argv, 0);
    JanetByteView joiner;
    if (argc == 2) {
        joiner = janet_getbytes(argv, 1);
    } else {
        joiner.bytes = NULL;
        joiner.len = 0;
    }
    /* Check args */
    int32_t i;
    int64_t finallen = 0;
    for (i = 0; i < parts.len; i++) {
        const uint8_t *chunk;
        int32_t chunklen = 0;
        if (!janet_bytes_view(parts.items[i], &chunk, &chunklen)) {
            janet_panicf("item %d of parts is not a byte sequence, got %v", i, parts.items[i]);
        }
        if (i) finallen += joiner.len;
        finallen += chunklen;
        if (finallen > INT32_MAX)
            janet_panic("result string too long");
    }
    uint8_t *buf, *out;
    out = buf = janet_string_begin((int32_t) finallen);
    for (i = 0; i < parts.len; i++) {
        const uint8_t *chunk = NULL;
        int32_t chunklen = 0;
        if (i) {
            memcpy(out, joiner.bytes, joiner.len);
            out += joiner.len;
        }
        janet_bytes_view(parts.items[i], &chunk, &chunklen);
        memcpy(out, chunk, chunklen);
        out += chunklen;
    }
    return janet_wrap_string(janet_string_end(buf));
}

static Janet cfun_string_format(int32_t argc, Janet *argv) {
    janet_arity(argc, 1, -1);
    JanetBuffer *buffer = janet_buffer(0);
    const char *strfrmt = (const char *) janet_getstring(argv, 0);
    janet_buffer_format(buffer, strfrmt, 0, argc, argv);
    return janet_stringv(buffer->data, buffer->count);
}

/*
 * code adapted from lua/lstrlib.c http://lua.org
 */


#define CAP_UNFINISHED  (-1)
#define CAP_POSITION    (-2)

#define MAXCAPTURES 256
#define MAXCCALLS 200
#define CHAR_ESC        '%'
#define SPECIALS    "^$*+?.([%-"

#define uchar(c)    ((unsigned char)(c))

typedef struct MatchState {
    const char *src_init;  /* init of source string */
    const char *src_end;  /* end ('\0') of source string */
    const char *p_end;  /* end ('\0') of pattern */
    int matchdepth;  /* control for recursive depth (to avoid C stack overflow) */
    unsigned char level;  /* total number of captures (finished or unfinished) */
    struct {
        const char *init;
        ptrdiff_t len;
    } capture[MAXCAPTURES];
} MatchState;


/* recursive function */
static const char *match(MatchState *ms, const char *s, const char *p);

static int check_capture(MatchState *ms, int l) {
    l -= '1';
    if (l < 0 || l >= ms->level || ms->capture[l].len == CAP_UNFINISHED)
        janet_panicf("invalid capture index %%%d", l + 1);
    return l;
}

static int capture_to_close(MatchState *ms) {
    int level = ms->level;
    for (level--; level >= 0; level--)
        if (ms->capture[level].len == CAP_UNFINISHED) return level;
    janet_panic("invalid pattern capture");
    return 0;
}


static const char *classend(MatchState *ms, const char *p) {
    switch (*p++) {
        case CHAR_ESC: {
            if (p == ms->p_end)
                janet_panic("malformed pattern (ends with '%%')");
            return p + 1;
        }
        case '[': {
            if (*p == '^') p++;
            do {  /* look for a ']' */
                if (p == ms->p_end)
                    janet_panic("malformed pattern (missing ']')");
                if (*(p++) == CHAR_ESC && p < ms->p_end)
                    p++;  /* skip escapes (e.g. '%]') */
            } while (*p != ']');
            return p + 1;
        }
        default: {
            return p;
        }
    }
}


static int match_class(int c, int cl) {
    int res;
    switch (tolower(cl)) {
        case 'a' :
            res = isalpha(c);
            break;
        case 'c' :
            res = iscntrl(c);
            break;
        case 'd' :
            res = isdigit(c);
            break;
        case 'g' :
            res = isgraph(c);
            break;
        case 'l' :
            res = islower(c);
            break;
        case 'p' :
            res = ispunct(c);
            break;
        case 's' :
            res = isspace(c);
            break;
        case 'u' :
            res = isupper(c);
            break;
        case 'w' :
            res = isalnum(c);
            break;
        case 'x' :
            res = isxdigit(c);
            break;
        case 'z' :
            res = (c == 0);
            break;  /* deprecated option */
        default:
            return (cl == c);
    }
    return (islower(cl) ? res : !res);
}


static int matchbracketclass(int c, const char *p, const char *ec) {
    int sig = 1;
    if (*(p + 1) == '^') {
        sig = 0;
        p++;  /* skip the '^' */
    }
    while (++p < ec) {
        if (*p == CHAR_ESC) {
            p++;
            if (match_class(c, uchar(*p)))
                return sig;
        } else if ((*(p + 1) == '-') && (p + 2 < ec)) {
            p += 2;
            if (uchar(*(p - 2)) <= c && c <= uchar(*p))
                return sig;
        } else if (uchar(*p) == c) return sig;
    }
    return !sig;
}


static int singlematch(MatchState *ms, const char *s, const char *p,
                       const char *ep) {
    if (s >= ms->src_end)
        return 0;
    else {
        int c = uchar(*s);
        switch (*p) {
            case '.':
                return 1;  /* matches any char */
            case CHAR_ESC:
                return match_class(c, uchar(*(p + 1)));
            case '[':
                return matchbracketclass(c, p, ep - 1);
            default:
                return (uchar(*p) == c);
        }
    }
}


static const char *matchbalance(MatchState *ms, const char *s,
                                const char *p) {
    if (p >= ms->p_end - 1)
        janet_panic("malformed pattern (missing arguments to '%%b')");
    if (*s != *p) return NULL;
    else {
        int b = *p;
        int e = *(p + 1);
        int cont = 1;
        while (++s < ms->src_end) {
            if (*s == e) {
                if (--cont == 0) return s + 1;
            } else if (*s == b) cont++;
        }
    }
    return NULL;  /* string ends out of balance */
}


static const char *max_expand(MatchState *ms, const char *s,
                              const char *p, const char *ep) {
    ptrdiff_t i = 0;  /* counts maximum expand for item */
    while (singlematch(ms, s + i, p, ep))
        i++;
    /* keeps trying to match with the maximum repetitions */
    while (i >= 0) {
        const char *res = match(ms, (s + i), ep + 1);
        if (res) return res;
        i--;  /* else didn't match; reduce 1 repetition to try again */
    }
    return NULL;
}


static const char *min_expand(MatchState *ms, const char *s,
                              const char *p, const char *ep) {
    for (;;) {
        const char *res = match(ms, s, ep + 1);
        if (res != NULL)
            return res;
        else if (singlematch(ms, s, p, ep))
            s++;  /* try with one more repetition */
        else return NULL;
    }
}


static const char *start_capture(MatchState *ms, const char *s,
                                 const char *p, int what) {
    const char *res;
    int level = ms->level;
    if (level >= MAXCAPTURES) janet_panic("too many captures");
    ms->capture[level].init = s;
    ms->capture[level].len = what;
    ms->level = level + 1;
    if ((res = match(ms, s, p)) == NULL) /* match failed? */
        ms->level--;  /* undo capture */
    return res;
}


static const char *end_capture(MatchState *ms, const char *s,
                               const char *p) {
    int l = capture_to_close(ms);
    const char *res;
    ms->capture[l].len = s - ms->capture[l].init;  /* close capture */
    if ((res = match(ms, s, p)) == NULL)  /* match failed? */
        ms->capture[l].len = CAP_UNFINISHED;  /* undo capture */
    return res;
}


static const char *match_capture(MatchState *ms, const char *s, int l) {
    size_t len;
    l = check_capture(ms, l);
    len = ms->capture[l].len;
    if ((size_t)(ms->src_end - s) >= len &&
            memcmp(ms->capture[l].init, s, len) == 0)
        return s + len;
    else return NULL;
}


static const char *match(MatchState *ms, const char *s, const char *p) {
    if (ms->matchdepth-- == 0)
        janet_panic("pattern too complex");
init: /* using goto's to optimize tail recursion */
    if (p != ms->p_end) {  /* end of pattern? */
        switch (*p) {
            case '(': {  /* start capture */
                if (*(p + 1) == ')')  /* position capture? */
                    s = start_capture(ms, s, p + 2, CAP_POSITION);
                else
                    s = start_capture(ms, s, p + 1, CAP_UNFINISHED);
                break;
            }
            case ')': {  /* end capture */
                s = end_capture(ms, s, p + 1);
                break;
            }
            case '$': {
                if ((p + 1) != ms->p_end)  /* is the '$' the last char in pattern? */
                    goto dflt;  /* no; go to default */
                s = (s == ms->src_end) ? s : NULL;  /* check end of string */
                break;
            }
            case CHAR_ESC: {  /* escaped sequences not in the format class[*+?-]? */
                switch (*(p + 1)) {
                    case 'b': {  /* balanced string? */
                        s = matchbalance(ms, s, p + 2);
                        if (s != NULL) {
                            p += 4;
                            goto init;  /* return match(ms, s, p + 4); */
                        }  /* else fail (s == NULL) */
                        break;
                    }
                    case 'f': {  /* frontier? */
                        const char *ep;
                        char previous;
                        p += 2;
                        if (*p != '[')
                            janet_panic("missing '[' after '%%f' in pattern");
                        ep = classend(ms, p);  /* points to what is next */
                        previous = (s == ms->src_init) ? '\0' : *(s - 1);
                        if (!matchbracketclass(uchar(previous), p, ep - 1) &&
                                matchbracketclass(uchar(*s), p, ep - 1)) {
                            p = ep;
                            goto init;  /* return match(ms, s, ep); */
                        }
                        s = NULL;  /* match failed */
                        break;
                    }
                    case '0':
                    case '1':
                    case '2':
                    case '3':
                    case '4':
                    case '5':
                    case '6':
                    case '7':
                    case '8':
                    case '9': {  /* capture results (%0-%9)? */
                        s = match_capture(ms, s, uchar(*(p + 1)));
                        if (s != NULL) {
                            p += 2;
                            goto init;  /* return match(ms, s, p + 2) */
                        }
                        break;
                    }
                    default:
                        goto dflt;
                }
                break;
            }
            default:
            dflt: {  /* pattern class plus optional suffix */
                    const char *ep = classend(ms, p);  /* points to optional suffix */
                    /* does not match at least once? */
                    if (!singlematch(ms, s, p, ep)) {
                        if (*ep == '*' || *ep == '?' || *ep == '-') {  /* accept empty? */
                            p = ep + 1;
                            goto init;  /* return match(ms, s, ep + 1); */
                        } else /* '+' or no suffix */
                            s = NULL;  /* fail */
                    } else { /* matched once */
                        switch (*ep) {  /* handle optional suffix */
                            case '?': {  /* optional */
                                const char *res;
                                if ((res = match(ms, s + 1, ep + 1)) != NULL)
                                    s = res;
                                else {
                                    p = ep + 1;
                                    goto init;  /* else return match(ms, s, ep + 1); */
                                }
                                break;
                            }
                            case '+':  /* 1 or more repetitions */
                                s++;  /* 1 match already done */
                            /* FALLTHROUGH */
                            case '*':  /* 0 or more repetitions */
                                s = max_expand(ms, s, p, ep);
                                break;
                            case '-':  /* 0 or more repetitions (minimum) */
                                s = min_expand(ms, s, p, ep);
                                break;
                            default:  /* no suffix */
                                s++;
                                p = ep;
                                goto init;  /* return match(ms, s + 1, ep); */
                        }
                    }
                    break;
                }
        }
    }
    ms->matchdepth++;
    return s;
}


static void push_onecapture(MatchState *ms, int i, const char *s,
                            const char *e, JanetArray *captures) {
    if (i >= ms->level) {
        if (i == 0)  /* ms->level == 0, too */
            janet_array_push(captures, janet_wrap_string(janet_string((uint8_t *)s, e - s))); /* add whole match */
        else
            janet_panicf("invalid capture index %%%d", i + 1);
    } else {
        ptrdiff_t l = ms->capture[i].len;
        if (l == CAP_UNFINISHED) janet_panic("unfinished capture");
        if (l == CAP_POSITION)
            janet_array_push(captures, janet_wrap_number((ms->capture[i].init - ms->src_init) + 1));
        else
            janet_array_push(captures, janet_wrap_string(janet_string((uint8_t *)(ms->capture[i].init), l)));
    }
}


static int push_captures(MatchState *ms, const char *s, const char *e, JanetArray *captures) {
    int i;
    int nlevels = (ms->level == 0 && s) ? 1 : ms->level;
    for (i = 0; i < nlevels; i++)
        push_onecapture(ms, i, s, e, captures);
    return nlevels;  /* number of strings pushed */
}



static void prepstate(MatchState *ms,
                      const char *s, size_t ls, const char *p, size_t lp) {
    ms->matchdepth = MAXCCALLS;
    ms->src_init = s;
    ms->src_end = s + ls;
    ms->p_end = p + lp;
}


static void reprepstate(MatchState *ms) {
    ms->level = 0;
    if (ms->matchdepth != MAXCCALLS) janet_panic("matchdepth error");
}


static size_t posrelatI(int pos, size_t len) {
    if (pos > 0)
        return (size_t)pos;
    else if (pos == 0)
        return 1;
    else if (pos < -(int)len)  /* inverted comparison */
        return 1;  /* clip to 1 */
    else return len + (size_t)pos + 1;
}

static Janet cfun_str_match(int32_t argc, Janet *argv) {
    janet_arity(argc, 2, 3);
    JanetByteView view = janet_getbytes(argv, 0);
    const char *s = (const char *) view.bytes;
    size_t ls = (size_t) view.len;
    const char *p = (const char *) janet_getstring(argv, 1);
    size_t lp = janet_string_length(p);
    size_t init = 0;
    if (argc == 3) {
        init = posrelatI(janet_getinteger(argv, 2), ls) - 1;
    }
    if (init > ls) {  /* start after string's end? */
        return janet_wrap_nil();  /* cannot find anything */
    }
    MatchState ms;
    const char *s1 = s + init;
    int anchor = (*p == '^');
    if (anchor) {
        p++;
        lp--;  /* skip anchor character */
    }
    prepstate(&ms, s, ls, p, lp);
    do {
        const char *res;
        reprepstate(&ms);
        if ((res = match(&ms, s1, p)) != NULL) {
            JanetArray *captures = janet_array(8);
            push_captures(&ms, s1, res, captures);
            return janet_wrap_array(captures);
        }
    } while (s1++ < ms.src_end && !anchor);

    return janet_wrap_nil();  /* not found */
}

static const JanetReg string_cfuns[] = {
    {
        "string/slice", cfun_string_slice,
        JDOC("(string/slice bytes [,start=0 [,end=(length str)]])\n\n"
             "Returns a substring from a byte sequence. The substring is from "
             "index start inclusive to index end exclusive. All indexing "
             "is from 0. 'start' and 'end' can also be negative to indicate indexing "
             "from the end of the string.")
    },
    {
        "string/repeat", cfun_string_repeat,
        JDOC("(string/repeat bytes n)\n\n"
             "Returns a string that is n copies of bytes concatenated.")
    },
    {
        "string/bytes", cfun_string_bytes,
        JDOC("(string/bytes str)\n\n"
             "Returns an array of integers that are the byte values of the string.")
    },
    {
        "string/from-bytes", cfun_string_frombytes,
        JDOC("(string/from-bytes byte-array)\n\n"
             "Creates a string from an array of integers with byte values. All integers "
             "will be coerced to the range of 1 byte 0-255.")
    },
    {
        "string/ascii-lower", cfun_string_asciilower,
        JDOC("(string/ascii-lower str)\n\n"
             "Returns a new string where all bytes are replaced with the "
             "lowercase version of themselves in ASCII. Does only a very simple "
             "case check, meaning no unicode support.")
    },
    {
        "string/ascii-upper", cfun_string_asciiupper,
        JDOC("(string/ascii-upper str)\n\n"
             "Returns a new string where all bytes are replaced with the "
             "uppercase version of themselves in ASCII. Does only a very simple "
             "case check, meaning no unicode support.")
    },
    {
        "string/reverse", cfun_string_reverse,
        JDOC("(string/reverse str)\n\n"
             "Returns a string that is the reversed version of str.")
    },
    {
        "string/find", cfun_string_find,
        JDOC("(string/find patt str)\n\n"
             "Searches for the first instance of pattern patt in string "
             "str. Returns the index of the first character in patt if found, "
             "otherwise returns nil.")
    },
    {
        "string/find-all", cfun_string_findall,
        JDOC("(string/find patt str)\n\n"
             "Searches for all instances of pattern patt in string "
             "str. Returns an array of all indices of found patterns. Overlapping "
             "instances of the pattern are not counted, meaning a byte in string "
             "will only contribute to finding at most on occurrence of pattern. If no "
             "occurrences are found, will return an empty array.")
    },
    {
        "string/replace", cfun_string_replace,
        JDOC("(string/replace patt subst str)\n\n"
             "Replace the first occurrence of patt with subst in the string str. "
             "Will return the new string if patt is found, otherwise returns str.")
    },
    {
        "string/replace-all", cfun_string_replaceall,
        JDOC("(string/replace-all patt subst str)\n\n"
             "Replace all instances of patt with subst in the string str. "
             "Will return the new string if patt is found, otherwise returns str.")
    },
    {
        "string/split", cfun_string_split,
        JDOC("(string/split delim str)\n\n"
             "Splits a string str with delimiter delim and returns an array of "
             "substrings. The substrings will not contain the delimiter delim. If delim "
             "is not found, the returned array will have one element.")
    },
    {
        "string/check-set", cfun_string_checkset,
        JDOC("(string/check-set set str)\n\n"
             "Checks if any of the bytes in the string set appear in the string str. "
             "Returns true if some bytes in set do appear in str, false if no bytes do.")
    },
    {
        "string/join", cfun_string_join,
        JDOC("(string/join parts [,sep])\n\n"
             "Joins an array of strings into one string, optionally separated by "
             "a separator string sep.")
    },
    {
        "string/format", cfun_string_format,
        JDOC("(string/format format & values)\n\n"
             "Similar to snprintf, but specialized for operating with janet. Returns "
             "a new string.")
    },
    {
        "string/match", cfun_str_match,
        JDOC("(string/match string pattern [start=1])\n\n"
             "return array with captures or nil.\n"
             "(lua style pattern matching)")
    },
    {NULL, NULL, NULL}
};

/* Module entry point */
void janet_lib_string(JanetTable *env) {
    janet_core_cfuns(env, NULL, string_cfuns);
}
