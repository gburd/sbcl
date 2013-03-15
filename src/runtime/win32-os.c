/*
 * the Win32 incarnation of OS-dependent routines.  See also
 * $(sbcl_arch)-win32-os.c
 *
 * This file (along with os.h) exports an OS-independent interface to
 * the operating system VM facilities. Surprise surprise, this
 * interface looks a lot like the Mach interface (but simpler in some
 * places). For some operating systems, a subset of these functions
 * will have to be emulated.
 */

/*
 * This software is part of the SBCL system. See the README file for
 * more information.
 *
 * This software is derived from the CMU CL system, which was
 * written at Carnegie Mellon University and released into the
 * public domain. The software is in the public domain and is
 * provided with absolutely no warranty. See the COPYING and CREDITS
 * files for more information.
 */

/*
 * This file was copied from the Linux version of the same, and
 * likely still has some linuxisms in it have haven't been elimiated
 * yet.
 */

#include <malloc.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/param.h>
#include <sys/file.h>
#include <io.h>
#include "sbcl.h"
#include "os.h"
#include "arch.h"
#include "globals.h"
#include "sbcl.h"
#include "interrupt.h"
#include "interr.h"
#include "lispregs.h"
#include "runtime.h"
#include "alloc.h"
#include "genesis/primitive-objects.h"
#include "dynbind.h"

#include <sys/types.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <unistd.h>

#include <math.h>
#include <float.h>

#include <excpt.h>
#include <errno.h>

#include "validate.h"
#include "thread.h"
#include "cpputil.h"

#ifndef LISP_FEATURE_SB_THREAD
/* dummy definition to reduce ifdef clutter */
#define WITH_GC_AT_SAFEPOINTS_ONLY() if (0) ; else
#endif

os_vm_size_t os_vm_page_size;

#include "gc.h"
#include "gencgc-internal.h"
#include <winsock2.h>
#include <wincrypt.h>

#if 0
int linux_sparc_siginfo_bug = 0;
int linux_supports_futex=0;
#endif

#include <stdarg.h>
#include <string.h>

/* missing definitions for modern mingws */
#ifndef EH_UNWINDING
#define EH_UNWINDING 0x02
#endif
#ifndef EH_EXIT_UNWIND
#define EH_EXIT_UNWIND 0x04
#endif

/* Tired of writing arch_os_get_current_thread each time. */
#define this_thread (arch_os_get_current_thread())

/* wrappers for winapi calls that must be successful (like SBCL's
 * (aver ...) form). */

/* win_aver function: basic building block for miscellaneous
 * ..AVER.. macrology (below) */

/* To do: These routines used to be "customizable" with dyndebug_init()
 * and variables like dyndebug_survive_aver, dyndebug_skip_averlax based
 * on environment variables.  Those features got lost on the way, but
 * ought to be reintroduced. */

static inline
intptr_t win_aver(intptr_t value, char* comment, char* file, int line,
                  int justwarn)
{
    if (!value) {
        LPSTR errorMessage = "<FormatMessage failed>";
        DWORD errorCode = GetLastError(), allocated=0;
        int posixerrno = errno;
        const char* posixstrerror = strerror(errno);
        char* report_template =
            "Expression unexpectedly false: %s:%d\n"
            " ... %s\n"
            "     ===> returned #X%p, \n"
            "     (in thread %p)"
            " ... Win32 thinks:\n"
            "     ===> code %u, message => %s\n"
            " ... CRT thinks:\n"
            "     ===> code %u, message => %s\n";

        allocated =
            FormatMessageA(FORMAT_MESSAGE_ALLOCATE_BUFFER|
                           FORMAT_MESSAGE_FROM_SYSTEM,
                           NULL,
                           errorCode,
                           MAKELANGID(LANG_ENGLISH,SUBLANG_ENGLISH_US),
                           (LPSTR)&errorMessage,
                           1024u,
                           NULL);

        if (justwarn) {
            fprintf(stderr, report_template,
                    file, line,
                    comment, value,
                    this_thread,
                    (unsigned)errorCode, errorMessage,
                    posixerrno, posixstrerror);
        } else {
            lose(report_template,
                    file, line,
                    comment, value,
                    this_thread,
                    (unsigned)errorCode, errorMessage,
                    posixerrno, posixstrerror);
        }
        if (allocated)
            LocalFree(errorMessage);
    }
    return value;
}

/* sys_aver function: really tiny adaptor of win_aver for
 * "POSIX-parody" CRT results ("lowio" and similar stuff):
 * negative number means something... negative. */
static inline
intptr_t sys_aver(long value, char* comment, char* file, int line,
              int justwarn)
{
    win_aver((intptr_t)(value>=0),comment,file,line,justwarn);
    return value;
}

/* Check for (call) result being boolean true. (call) may be arbitrary
 * expression now; massive attack of gccisms ensures transparent type
 * conversion back and forth, so the type of AVER(expression) is the
 * type of expression. Value is the same _if_ it can be losslessly
 * converted to (void*) and back.
 *
 * Failed AVER() is normally fatal. Well, unless dyndebug_survive_aver
 * flag is set. */

#define AVER(call)                                                      \
    ({ __typeof__(call) __attribute__((unused)) me =                    \
            (__typeof__(call))                                          \
            win_aver((intptr_t)(call), #call, __FILE__, __LINE__, 0);      \
        me;})

/* AVERLAX(call): do the same check as AVER did, but be mild on
 * failure: print an annoying unrequested message to stderr, and
 * continue. With dyndebug_skip_averlax flag, AVERLAX stop even to
 * check and complain. */

#define AVERLAX(call)                                                   \
    ({ __typeof__(call) __attribute__((unused)) me =                    \
            (__typeof__(call))                                          \
            win_aver((intptr_t)(call), #call, __FILE__, __LINE__, 1);      \
        me;})

/* Now, when failed AVER... prints both errno and GetLastError(), two
 * variants of "POSIX/lowio" style checks below are almost useless
 * (they build on sys_aver like the two above do on win_aver). */

#define CRT_AVER_NONNEGATIVE(call)                              \
    ({ __typeof__(call) __attribute__((unused)) me =            \
            (__typeof__(call))                                  \
            sys_aver((call), #call, __FILE__, __LINE__, 0);     \
        me;})

#define CRT_AVERLAX_NONNEGATIVE(call)                           \
    ({ __typeof__(call) __attribute__((unused)) me =            \
            (__typeof__(call))                                  \
            sys_aver((call), #call, __FILE__, __LINE__, 1);     \
        me;})

/* to be removed */
#define CRT_AVER(booly)                                         \
    ({ __typeof__(booly) __attribute__((unused)) me = (booly);  \
        sys_aver((booly)?0:-1, #booly, __FILE__, __LINE__, 0);  \
        me;})

const char * t_nil_s(lispobj symbol);

/*
 * The following signal-mask-related alien routines are called from Lisp:
 */

/* As of win32, deferrables _do_ matter. gc_signal doesn't. */
unsigned long block_deferrables_and_return_mask()
{
    sigset_t sset;
    block_deferrable_signals(0, &sset);
    return (unsigned long)sset;
}

#if defined(LISP_FEATURE_SB_THREAD)
void apply_sigmask(unsigned long sigmask)
{
    sigset_t sset = (sigset_t)sigmask;
    pthread_sigmask(SIG_SETMASK, &sset, 0);
}
#endif

/* The exception handling function looks like this: */
EXCEPTION_DISPOSITION handle_exception(EXCEPTION_RECORD *,
                                       struct lisp_exception_frame *,
                                       CONTEXT *,
                                       void *);
/* handle_exception is defined further in this file, but since SBCL
 * 1.0.1.24, it doesn't get registered as SEH handler directly anymore,
 * not even by wos_install_interrupt_handlers. Instead, x86-assem.S
 * provides exception_handler_wrapper; we install it here, and each
 * exception frame on nested funcall()s also points to it.
 */


void *base_seh_frame;

HMODULE runtime_module_handle = 0u;

static void *get_seh_frame(void)
{
    void* retval;
#ifdef LISP_FEATURE_X86
    asm volatile ("mov %%fs:0,%0": "=r" (retval));
#else
    asm volatile ("mov %%gs:0,%0": "=r" (retval));
#endif
    return retval;
}

static void set_seh_frame(void *frame)
{
#ifdef LISP_FEATURE_X86
    asm volatile ("mov %0,%%fs:0": : "r" (frame));
#else
    asm volatile ("mov %0,%%gs:0": : "r" (frame));
#endif
}

#if defined(LISP_FEATURE_SB_THREAD)

void alloc_gc_page()
{
    AVER(VirtualAlloc(GC_SAFEPOINT_PAGE_ADDR, sizeof(lispobj),
                      MEM_RESERVE|MEM_COMMIT, PAGE_READWRITE));
}

/* Permit loads from GC_SAFEPOINT_PAGE_ADDR (NB page state change is
 * "synchronized" with the memory region content/availability --
 * e.g. you won't see other CPU flushing buffered writes after WP --
 * but there is some window when other thread _seem_ to trap AFTER
 * access is granted. You may think of it something like "OS enters
 * SEH handler too slowly" -- what's important is there's no implicit
 * synchronization between VirtualProtect caller and other thread's
 * SEH handler, hence no ordering of events. VirtualProtect is
 * implicitly synchronized with protected memory contents (only).
 *
 * The last fact may be potentially used with many benefits e.g. for
 * foreign call speed, but we don't use it for now: almost the only
 * fact relevant to the current signalling protocol is "sooner or
 * later everyone will trap [everyone will stop trapping]".
 *
 * An interesting source on page-protection-based inter-thread
 * communication is a well-known paper by Dave Dice, Hui Huang,
 * Mingyao Yang: ``Asymmetric Dekker Synchronization''. Last time
 * I checked it was available at
 * http://home.comcast.net/~pjbishop/Dave/Asymmetric-Dekker-Synchronization.txt
 */
void map_gc_page()
{
    DWORD oldProt;
    AVER(VirtualProtect((void*) GC_SAFEPOINT_PAGE_ADDR, sizeof(lispobj),
                        PAGE_READWRITE, &oldProt));
}

void unmap_gc_page()
{
    DWORD oldProt;
    AVER(VirtualProtect((void*) GC_SAFEPOINT_PAGE_ADDR, sizeof(lispobj),
                        PAGE_NOACCESS, &oldProt));
}

#endif

#if defined(LISP_FEATURE_SB_DYNAMIC_CORE)
/* This feature has already saved me more development time than it
 * took to implement.  In its current state, ``dynamic RT<->core
 * linking'' is a protocol of initialization of C runtime and Lisp
 * core, populating SBCL linkage table with entries for runtime
 * "foreign" symbols that were referenced in cross-compiled code.
 *
 * How it works: a sketch
 *
 * Last Genesis (resulting in cold-sbcl.core) binds foreign fixups in
 * x-compiled lisp-objs to sequential addresses from the beginning of
 * linkage-table space; that's how it ``resolves'' foreign references.
 * Obviously, this process doesn't require pre-built runtime presence.
 *
 * When the runtime loads the core (cold-sbcl.core initially,
 * sbcl.core later), runtime should do its part of the protocol by (1)
 * traversing a list of ``runtime symbols'' prepared by Genesis and
 * dumped as a static symbol value, (2) resolving each name from this
 * list to an address (stubbing unresolved ones with
 * undefined_alien_address or undefined_alien_function), (3) adding an
 * entry for each symbol somewhere near the beginning of linkage table
 * space (location is provided by the core).
 *
 * The implementation of the part described in the last paragraph
 * follows. C side is currently more ``hackish'' and less clear than
 * the Lisp code; OTOH, related Lisp changes are scattered, and some
 * of them play part in complex interrelations -- beautiful but taking
 * much time to understand --- but my subset of PE-i386 parser below
 * is in one place (here) and doesn't have _any_ non-trivial coupling
 * with the rest of the Runtime.
 *
 * What do we gain with this feature, after all?
 *
 * One things that I have to do rather frequently: recompile and
 * replace runtime without rebuilding the core. Doubtlessly, slam.sh
 * was a great time-saver here, but relinking ``cold'' core and bake a
 * ``warm'' one takes, as it seems, more than 10x times of bare
 * SBCL.EXE build time -- even if everything is recompiled, which is
 * now unnecessary. Today, if I have a new idea for the runtime,
 * getting from C-x C-s M-x ``compile'' to fully loaded SBCL
 * installation takes 5-15 seconds.
 *
 * Another thing (that I'm not currently using, but obviously
 * possible) is delivering software patches to remote system on
 * customer site. As you are doing minor additions or corrections in
 * Lisp code, it doesn't take much effort to prepare a tiny ``FASL
 * bundle'' that rolls up your patch, redumps and -- presto -- 100MiB
 * program is fixed by sending and loading a 50KiB thingie.
 *
 * However, until LISP_FEATURE_SB_DYNAMIC_CORE, if your bug were fixed
 * by modifying two lines of _C_ sources, a customer described above
 * had to be ready to receive and reinstall a new 100MiB
 * executable. With the aid of code below, deploying such a fix
 * requires only sending ~300KiB (when stripped) of SBCL.EXE.
 *
 * But there is more to it: as the common linkage-table is used for
 * DLLs and core, its entries may be overridden almost without a look
 * into SBCL internals. Therefore, ``patching'' C runtime _without_
 * restarting target systems is also possible in many situations
 * (it's not as trivial as loading FASLs into a running daemon, but
 * easy enough to be a viable alternative if any downtime is highly
 * undesirable).
 *
 * During my (rather limited) commercial Lisp development experience
 * I've already been through a couple of situations where such
 * ``deployment'' issues were important; from my _total_ programming
 * experience I know -- _sometimes_ they are a two orders of magnitude
 * more important than those I observed.
 *
 * The possibility of entire runtime ``hot-swapping'' in running
 * process is not purely theoretical, as it could seem. There are 2-3
 * problems whose solution is not obvious (call stack patching, for
 * instance), but it's literally _nothing_ if compared with
 * e.g. LISP_FEATURE_SB_AUTO_FPU_SWITCH.  By the way, one of the
 * problems with ``hot-swapping'', that could become a major one in
 * many other environments, is nonexistent in SBCL: we already have a
 * ``global quiesce point'' that is generally required for this kind
 * of worldwide revolution -- around collect_garbage.
 *
 * What's almost unnoticeable from the C side (where you are now, dear
 * reader): using the same style for all linking is beautiful. I tried
 * to leave old-style linking code in place for the sake of
 * _non-linkage-table_ platforms (they probably don't have -ldl or its
 * equivalent, like LL/GPA, at all) -- but i did it usually by moving
 * the entire `old style' code under #!-sb-dynamic-core and
 * refactoring the `new style' branch, instead of cutting the tail
 * piecemeal and increasing #!+-ifdeffery amount & the world enthropy.
 *
 * If we look at the majority of the ``new style'' code units, it's a
 * common thing to observe how #!+-ifdeffery _vanishes_ instead of
 * multiplying: #!-sb-xc, #!+sb-xc-host and #!-sb-xc-host end up
 * needing the same code. Runtime checks of static v. dynamic symbol
 * disappear even faster. STDCALL mangling and leading underscores go
 * out of scope (and GCed, hopefully) instead of surfacing here and
 * there as a ``special case for core static symbols''. What I like
 * the most about CL development in general is a frequency of solving
 * problems and fixing bugs by simplifying code and dropping special
 * cases.
 *
 * Last important thing about the following code: besides resolving
 * symbols provided by the core itself, it detects runtime's own
 * build-time prerequisite DLLs. Any symbol that is unresolved against
 * the core is looked up in those DLLs (normally kernel32, msvcrt,
 * ws2_32... I could forget something). This action (1) resembles
 * implementation of foreign symbol lookup in SBCL itself, (2)
 * emulates shared library d.l. facilities of OSes that use flat
 * dynamic symbol namespace (or default to it). Anyone concerned with
 * portability problems of this PE-i386 stuff below will be glad to
 * hear that it could be ported to most modern Unices _by deletion_:
 * raw dlsym() with null handle usually does the same thing that i'm
 * trying to squeeze out of MS Windows by the brute force.
 *
 * My reason for _desiring_ flat symbol namespace, populated from
 * link-time dependencies, is avoiding any kind of ``requested-by-Lisp
 * symbol lists to be linked statically'', providing core v. runtime
 * independence in both directions. Minimizing future maintenance
 * effort is very important; I had gone for it consistently, starting
 * by turning "CloseHandle@4" into a simple "CloseHandle", continuing
 * by adding intermediate Genesis resulting in autogenerated symbol
 * list (farewell, void scratch(); good riddance), going to take
 * another great step for core/runtime independence... and _without_
 * flat namespace emulation, the ghosts and spirits exiled at the
 * first steps would come and take revenge: well, here are the symbols
 * that are really in msvcrt.dll.. hmm, let's link statically against
 * them, so the entry is pulled from the import library.. and those
 * entry has mangled names that we have to map.. ENOUGH, I though
 * here: fed up with stuff like that.
 *
 * Now here we are, without import libraries, without mangled symbols,
 * and without nm-generated symbol tables. Every symbol exported by
 * the runtime is added to SBCL.EXE export directory; every symbol
 * requested by the core is looked up by GetProcAddress for SBCL.EXE,
 * falling back to GetProcAddress for MSVCRT.dll, etc etc.. All ties
 * between SBCL's foreign symbols with object file symbol tables,
 * import libraries and other pre-linking symbol-resolving entities
 * _having no representation in SBCL.EXE_ were teared.
 *
 * This simplistic approach proved to work well; there is only one
 * problem introduced by it, and rather minor: in real MSVCRT.dll,
 * what's used to be available as open() is now called _open();
 * similar thing happened to many other `lowio' functions, though not
 * every one, so it's not a kind of name mangling but rather someone's
 * evil creative mind in action.
 *
 * When we look up any of those poor `uglified' functions in CRT
 * reference on MSDN, we can see a notice resembling this one:
 *
 * `unixishname()' is obsolete and provided for backward
 * compatibility; new standard-compliant function, `_unixishname()',
 * should be used instead.  Sentences of that kind were there for
 * several years, probably even for a decade or more (a propos,
 * MSVCRT.dll, as the name to link against, predates year 2000, so
 * it's actually possible). Reasoning behing it (what MS people had in
 * mind) always seemed strange to me: if everyone uses open() and that
 * `everyone' is important to you, why rename the function?  If no one
 * uses open(), why provide or retain _open() at all? <kidding>After
 * all, names like _open() are entirely non-informative and just plain
 * ugly; compare that with CreateFileW() or InitCommonControlsEx(),
 * the real examples of beauty and clarity.</kidding>
 *
 * Anyway, if the /standard/ name on Windows is _open() (I start to
 * recall, vaguely, that it's because of _underscore names being
 * `reserved to system' and all other ones `available for user', per
 * ANSI/ISO C89) -- well, if the /standard/ name is _open, SBCL should
 * use it when it uses MSVCRT and not some ``backward-compatible''
 * stuff. Deciding this way, I added a hack to SBCL's syscall macros,
 * so "[_]open" as a syscall name is interpreted as a request to link
 * agains "_open" on win32 and "open" on every other system.
 *
 * Of course, this name-parsing trick lacks conceptual clarity; we're
 * going to get rid of it eventually. */

u32 os_get_build_time_shared_libraries(u32 excl_maximum,
                                       void* opt_root,
                                       void** opt_store_handles,
                                       const char *opt_store_names[])
{
    void* base = opt_root ? opt_root : (void*)runtime_module_handle;
    /* base defaults to 0x400000 with GCC/mingw32. If you dereference
     * that location, you'll see 'MZ' bytes */
    void* base_magic_location =
        base + ((IMAGE_DOS_HEADER*)base)->e_lfanew;

    /* dos header provided the offset from `base' to
     * IMAGE_FILE_HEADER where PE-i386 really starts */

    void* check_duplicates[excl_maximum];

    if ((*(u32*)base_magic_location)!=0x4550) {
        /* We don't need this DLL thingie _that_ much. If the world
         * has changed to a degree where PE magic isn't found, let's
         * silently return `no libraries detected'. */
        return 0;
    } else {
        /* We traverse PE-i386 structures of SBCL.EXE in memory (not
         * in the file). File and memory layout _surely_ differ in
         * some places and _may_ differ in some other places, but
         * fortunately, those places are irrelevant to the task at
         * hand. */

        IMAGE_FILE_HEADER* image_file_header = (base_magic_location + 4);
        IMAGE_OPTIONAL_HEADER* image_optional_header =
            (void*)(image_file_header + 1);
        IMAGE_DATA_DIRECTORY* image_import_direntry =
            &image_optional_header->DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
        IMAGE_IMPORT_DESCRIPTOR* image_import_descriptor =
            base + image_import_direntry->VirtualAddress;
        u32 nlibrary, i,j;

        for (nlibrary=0u; nlibrary < excl_maximum
                          && image_import_descriptor->FirstThunk;
             ++image_import_descriptor)
        {
            HMODULE hmodule;
            odxprint(runtime_link, "Now should know DLL: %s",
                     (char*)(base + image_import_descriptor->Name));
            /* Code using image thunk data to get its handle was here, with a
             * number of platform-specific tricks (like using VirtualQuery for
             * old OSes lacking GetModuleHandleEx).
             *
             * It's now replaced with requesting handle by name, which is
             * theoretically unreliable (with SxS, multiple modules with same
             * name are quite possible), but good enough to find the
             * link-time dependencies of our executable or DLL. */

            hmodule = (HMODULE)
                GetModuleHandle(base + image_import_descriptor->Name);

            if (hmodule)
            {
                /* We may encouncer some module more than once while
                   traversing import descriptors (it's usually a
                   result of non-trivial linking process, like doing
                   ld -r on some groups of files before linking
                   everything together.

                   Anyway: using a module handle more than once will
                   do no harm, but it slows down the startup (even
                   now, our startup time is not a pleasant topic to
                   discuss when it comes to :sb-dynamic-core; there is
                   an obvious direction to go for speed, though --
                   instead of resolving symbols one-by-one, locate PE
                   export directories -- they are sorted by symbol
                   name -- and merge them, at one pass, with sorted
                   list of required symbols (the best time to sort the
                   latter list is during Genesis -- that's why I don't
                   proceed with memory copying, qsort() and merge
                   right here)). */

                for (j=0; j<nlibrary; ++j)
                {
                    if(check_duplicates[j] == hmodule)
                        break;
                }
                if (j<nlibrary) continue; /* duplicate => skip it in
                                           * outer loop */

                check_duplicates[nlibrary] = hmodule;
                if (opt_store_handles) {
                    opt_store_handles[nlibrary] = hmodule;
                }
                if (opt_store_names) {
                    opt_store_names[nlibrary] = (const char *)
                        (base + image_import_descriptor->Name);
                }
                odxprint(runtime_link, "DLL detection: %u, base %p: %s",
                         nlibrary, hmodule,
                         (char*)(base + image_import_descriptor->Name));
                ++ nlibrary;
            }
        }
        return nlibrary;
    }
}

static u32 buildTimeImageCount = 0;
static void* buildTimeImages[16];

/* Resolve symbols against the executable and its build-time dependencies */
void* os_dlsym_default(char* name)
{
    unsigned int i;
    void* result = 0;
    if (buildTimeImageCount == 0) {
        buildTimeImageCount =
            1 + os_get_build_time_shared_libraries(15u,
            NULL, 1+(void**)buildTimeImages, NULL);
    }
    for (i = 0; i<buildTimeImageCount && (!result); ++i) {
        result = GetProcAddress(buildTimeImages[i], name);
    }
    return result;
}

#endif /* SB_DYNAMIC_CORE */

#if defined(LISP_FEATURE_SB_THREAD)
/* We want to get a slot in TIB that (1) is available at constant
   offset, (2) is our private property, so libraries wouldn't legally
   override it, (3) contains something predefined for threads created
   out of our sight.

   Low 64 TLS slots are adressable directly, starting with
   FS:[#xE10]. When SBCL runtime is initialized, some of the low slots
   may be already in use by its prerequisite DLLs, as DllMain()s and
   TLS callbacks have been called already. But slot 63 is unlikely to
   be reached at this point: one slot per DLL that needs it is the
   common practice, and many system DLLs use predefined TIB-based
   areas outside conventional TLS storage and don't need TLS slots.
   With our current dependencies, even slot 2 is observed to be free
   (as of WinXP and wine).

   Now we'll call TlsAlloc() repeatedly until slot 63 is officially
   assigned to us, then TlsFree() all other slots for normal use. TLS
   slot 63, alias FS:[#.(+ #xE10 (* 4 63))], now belongs to us.

   To summarize, let's list the assumptions we make:

   - TIB, which is FS segment base, contains first 64 TLS slots at the
   offset #xE10 (i.e. TIB layout compatibility);
   - TLS slots are allocated from lower to higher ones;
   - All libraries together with CRT startup have not requested 64
   slots yet.

   All these assumptions together don't seem to be less warranted than
   the availability of TIB arbitrary data slot for our use. There are
   some more reasons to prefer slot 63 over TIB arbitrary data: (1) if
   our assumptions for slot 63 are violated, it will be detected at
   startup instead of causing some system-specific unreproducible
   problems afterwards, depending on OS and loaded foreign libraries;
   (2) if getting slot 63 reliably with our current approach will
   become impossible for some future Windows version, we can add TLS
   callback directory to SBCL binary; main image TLS callback is
   started before _any_ TLS slot is allocated by libraries, and
   some C compiler vendors rely on this fact. */

void os_preinit()
{
#ifdef LISP_FEATURE_X86
    DWORD slots[TLS_MINIMUM_AVAILABLE];
    DWORD key;
    int n_slots = 0, i;
    for (i=0; i<TLS_MINIMUM_AVAILABLE; ++i) {
        key = TlsAlloc();
        if (key == OUR_TLS_INDEX) {
            if (TlsGetValue(key)!=NULL)
                lose("TLS slot assertion failed: fresh slot value is not NULL");
            TlsSetValue(OUR_TLS_INDEX, (void*)(intptr_t)0xFEEDBAC4);
            if ((intptr_t)(void*)arch_os_get_current_thread()!=(intptr_t)0xFEEDBAC4)
                lose("TLS slot assertion failed: TIB layout change detected");
            TlsSetValue(OUR_TLS_INDEX, NULL);
            break;
        }
        slots[n_slots++]=key;
    }
    for (i=0; i<n_slots; ++i) {
        TlsFree(slots[i]);
    }
    if (key!=OUR_TLS_INDEX) {
        lose("TLS slot assertion failed: slot 63 is unavailable "
             "(last TlsAlloc() returned %u)",key);
    }
#endif
}
#endif  /* LISP_FEATURE_SB_THREAD */


#ifdef LISP_FEATURE_X86_64
/* Windows has 32-bit 'longs', so printf...%lX (and other %l patterns) doesn't
 * work well with address-sized values, like it's done all over the place in
 * SBCL. And msvcrt uses I64, not LL, for printing long longs.
 *
 * I've already had enough search/replace with longs/words/intptr_t for today,
 * so I prefer to solve this problem with a format string translator. */

/* There is (will be) defines for printf and friends. */

static int translating_vfprintf(FILE*stream, const char *fmt, va_list args)
{
    char translated[1024];
    int i=0, delta = 0;

    while (fmt[i-delta] && i<sizeof(translated)-1) {
        if((fmt[i-delta]=='%')&&
           (fmt[i-delta+1]=='l')) {
            translated[i++]='%';
            translated[i++]='I';
            translated[i++]='6';
            translated[i++]='4';
            delta += 2;
        } else {
            translated[i]=fmt[i-delta];
            ++i;
        }
    }
    translated[i++]=0;
    return vfprintf(stream,translated,args);
}

int printf(const char*fmt,...)
{
    va_list args;
    va_start(args,fmt);
    return translating_vfprintf(stdout,fmt,args);
}
int fprintf(FILE*stream,const char*fmt,...)
{
    va_list args;
    va_start(args,fmt);
    return translating_vfprintf(stream,fmt,args);
}

#endif

int os_number_of_processors = 1;

BOOL WINAPI CancelIoEx(HANDLE handle, LPOVERLAPPED overlapped);
typeof(CancelIoEx) *ptr_CancelIoEx;
BOOL WINAPI CancelSynchronousIo(HANDLE threadHandle);
typeof(CancelSynchronousIo) *ptr_CancelSynchronousIo;

#define RESOLVE(hmodule,fn)                     \
    do {                                        \
        ptr_##fn = (typeof(ptr_##fn))           \
            GetProcAddress(hmodule,#fn);        \
    } while (0)

static void resolve_optional_imports()
{
    HMODULE kernel32 = GetModuleHandleA("kernel32");
    if (kernel32) {
        RESOLVE(kernel32,CancelIoEx);
        RESOLVE(kernel32,CancelSynchronousIo);
    }
}

#undef RESOLVE

intptr_t win32_get_module_handle_by_address(os_vm_address_t addr)
{
    HMODULE result = 0;
    /* So apparently we could use VirtualQuery instead of
     * GetModuleHandleEx if we wanted to support pre-XP, pre-2003
     * versions of Windows (i.e. Windows 2000).  I've opted against such
     * special-casing. :-).  --DFL */
    return (intptr_t)(GetModuleHandleEx(
                          GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS |
                          GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
                          (LPCSTR)addr, &result)
                      ? result : 0);
}

void os_init(char *argv[], char *envp[])
{
    SYSTEM_INFO system_info;
    GetSystemInfo(&system_info);
    os_vm_page_size = system_info.dwPageSize > BACKEND_PAGE_BYTES?
        system_info.dwPageSize : BACKEND_PAGE_BYTES;
#if defined(LISP_FEATURE_X86)
    fast_bzero_pointer = fast_bzero_detect;
#endif
    os_number_of_processors = system_info.dwNumberOfProcessors;

    base_seh_frame = get_seh_frame();

    resolve_optional_imports();
    runtime_module_handle = (HMODULE)win32_get_module_handle_by_address(&runtime_module_handle);
}

static inline boolean local_thread_stack_address_p(os_vm_address_t address)
{
    return this_thread &&
        (((((u64)address >= (u64)this_thread->os_address) &&
           ((u64)address < ((u64)this_thread)-THREAD_CSP_PAGE_SIZE))||
          (((u64)address >= (u64)this_thread->control_stack_start)&&
           ((u64)address < (u64)this_thread->control_stack_end))));
}

/*
 * So we have three fun scenarios here.
 *
 * First, we could be being called to reserve the memory areas
 * during initialization (prior to loading the core file).
 *
 * Second, we could be being called by the GC to commit a page
 * that has just been decommitted (for easy zero-fill).
 *
 * Third, we could be being called by create_thread_struct()
 * in order to create the sundry and various stacks.
 *
 * The third case is easy to pick out because it passes an
 * addr of 0.
 *
 * The second case is easy to pick out because it will be for
 * a range of memory that is MEM_RESERVE rather than MEM_FREE.
 *
 * The second case is also an easy implement, because we leave
 * the memory as reserved (since we do lazy commits).
 */

os_vm_address_t
os_validate(os_vm_address_t addr, os_vm_size_t len)
{
    MEMORY_BASIC_INFORMATION mem_info;

    if (!addr) {
        /* the simple case first */
        return
            AVERLAX(VirtualAlloc(addr, len, MEM_RESERVE|MEM_COMMIT, PAGE_EXECUTE_READWRITE));
    }

    if (!AVERLAX(VirtualQuery(addr, &mem_info, sizeof mem_info)))
        return 0;

    if ((mem_info.State == MEM_RESERVE) && (mem_info.RegionSize >=len)) {
      /* It would be correct to return here. However, support for Wine
       * is beneficial, and Wine has a strange behavior in this
       * department. It reports all memory below KERNEL32.DLL as
       * reserved, but disallows MEM_COMMIT.
       *
       * Let's work around it: reserve the region we need for a second
       * time. The second reservation is documented to fail on normal NT
       * family, but it will succeed on Wine if this region is
       * actually free.
       */
      VirtualAlloc(addr, len, MEM_RESERVE, PAGE_EXECUTE_READWRITE);
      /* If it is wine, the second call has succeded, and now the region
       * is really reserved. */
      return addr;
    }

    if (mem_info.State == MEM_RESERVE) {
        fprintf(stderr, "validation of reserved space too short.\n");
        fflush(stderr);
        /* Oddly, we do not treat this assertion as fatal; hence also the
         * provision for MEM_RESERVE in the following code, I suppose: */
    }

    if (!AVERLAX(VirtualAlloc(addr, len, (mem_info.State == MEM_RESERVE)?
                              MEM_COMMIT: MEM_RESERVE, PAGE_EXECUTE_READWRITE)))
        return 0;

    return addr;
}

/*
 * For os_invalidate(), we merely decommit the memory rather than
 * freeing the address space. This loses when freeing per-thread
 * data and related memory since it leaks address space.
 *
 * So far the original comment (author unknown).  It used to continue as
 * follows:
 *
 *   It's not too lossy, however, since the two scenarios I'm aware of
 *   are fd-stream buffers, which are pooled rather than torched, and
 *   thread information, which I hope to pool (since windows creates
 *   threads at its own whim, and we probably want to be able to have
 *   them callback without funky magic on the part of the user, and
 *   full-on thread allocation is fairly heavyweight).
 *
 * But: As it turns out, we are no longer content with decommitting
 * without freeing, and have now grown a second function
 * os_invalidate_free(), sort of a really_os_invalidate().
 *
 * As discussed on #lisp, this is not a satisfactory solution, and probably
 * ought to be rectified in the following way:
 *
 *  - Any cases currently going through the non-freeing version of
 *    os_invalidate() are ultimately meant for zero-filling applications.
 *    Replace those use cases with an os_revalidate_bzero() or similarly
 *    named function, which explicitly takes care of that aspect of
 *    the semantics.
 *
 *  - The remaining uses of os_invalidate should actually free, and once
 *    the above is implemented, we can rename os_invalidate_free back to
 *    just os_invalidate().
 *
 * So far the new plan, as yet unimplemented. -- DFL
 */

void
os_invalidate(os_vm_address_t addr, os_vm_size_t len)
{
    AVERLAX(VirtualFree(addr, len, MEM_DECOMMIT));
}

void
os_invalidate_free(os_vm_address_t addr, os_vm_size_t len)
{
    AVERLAX(VirtualFree(addr, 0, MEM_RELEASE));
}

void
os_invalidate_free_by_any_address(os_vm_address_t addr, os_vm_size_t len)
{
    MEMORY_BASIC_INFORMATION minfo;
    AVERLAX(VirtualQuery(addr, &minfo, sizeof minfo));
    AVERLAX(minfo.AllocationBase);
    AVERLAX(VirtualFree(minfo.AllocationBase, 0, MEM_RELEASE));
}

/* os_validate doesn't commit, i.e. doesn't actually "validate" in the
 * sense that we could start using the space afterwards.  Usually it's
 * os_map or Lisp code that will run into that, in which case we recommit
 * elsewhere in this file.  For cases where C wants to write into newly
 * os_validate()d memory, it needs to commit it explicitly first:
 */
os_vm_address_t
os_validate_recommit(os_vm_address_t addr, os_vm_size_t len)
{
    return
        AVERLAX(VirtualAlloc(addr, len, MEM_COMMIT, PAGE_EXECUTE_READWRITE));
}

/*
 * os_map() is called to map a chunk of the core file into memory.
 *
 * Unfortunately, Windows semantics completely screws this up, so
 * we just add backing store from the swapfile to where the chunk
 * goes and read it up like a normal file. We could consider using
 * a lazy read (demand page) setup, but that would mean keeping an
 * open file pointer for the core indefinately (and be one more
 * thing to maintain).
 */

os_vm_address_t
os_map(int fd, int offset, os_vm_address_t addr, os_vm_size_t len)
{
    os_vm_size_t count;

    AVER(VirtualAlloc(addr, len, MEM_COMMIT, PAGE_EXECUTE_READWRITE)||
         VirtualAlloc(addr, len, MEM_RESERVE|MEM_COMMIT,
                      PAGE_EXECUTE_READWRITE));

    CRT_AVER_NONNEGATIVE(lseek(fd, offset, SEEK_SET));

    count = read(fd, addr, len);
    CRT_AVER( count == len );

    return addr;
}

static DWORD os_protect_modes[8] = {
    PAGE_NOACCESS,
    PAGE_READONLY,
    PAGE_READWRITE,
    PAGE_READWRITE,
    PAGE_EXECUTE,
    PAGE_EXECUTE_READ,
    PAGE_EXECUTE_READWRITE,
    PAGE_EXECUTE_READWRITE,
};

void
os_protect(os_vm_address_t address, os_vm_size_t length, os_vm_prot_t prot)
{
    DWORD old_prot;

    DWORD new_prot = os_protect_modes[prot];
    AVER(VirtualProtect(address, length, new_prot, &old_prot)||
         (VirtualAlloc(address, length, MEM_COMMIT, new_prot) &&
          VirtualProtect(address, length, new_prot, &old_prot)));
    odxprint(misc,"Protecting %p + %p vmaccess %d "
             "newprot %08x oldprot %08x",
             address,length,prot,new_prot,old_prot);
}

/* FIXME: Now that FOO_END, rather than FOO_SIZE, is the fundamental
 * description of a space, we could probably punt this and just do
 * (FOO_START <= x && x < FOO_END) everywhere it's called. */
static boolean
in_range_p(os_vm_address_t a, lispobj sbeg, size_t slen)
{
    char* beg = (char*)((uword_t)sbeg);
    char* end = (char*)((uword_t)sbeg) + slen;
    char* adr = (char*)a;
    return (adr >= beg && adr < end);
}

boolean
is_linkage_table_addr(os_vm_address_t addr)
{
    return in_range_p(addr, LINKAGE_TABLE_SPACE_START, LINKAGE_TABLE_SPACE_END);
}

static boolean is_some_thread_local_addr(os_vm_address_t addr);

boolean
is_valid_lisp_addr(os_vm_address_t addr)
{
    if(in_range_p(addr, READ_ONLY_SPACE_START, READ_ONLY_SPACE_SIZE) ||
       in_range_p(addr, STATIC_SPACE_START   , STATIC_SPACE_SIZE) ||
       in_range_p(addr, DYNAMIC_SPACE_START  , dynamic_space_size) ||
       is_some_thread_local_addr(addr))
        return 1;
    return 0;
}

/* test if an address is within thread-local space */
static boolean
is_thread_local_addr(struct thread* th, os_vm_address_t addr)
{
    /* Assuming that this is correct, it would warrant further comment,
     * I think.  Based on what our call site is doing, we have been
     * tasked to check for the address of a lisp object; not merely any
     * foreign address within the thread's area.  Indeed, this used to
     * be a check for control and binding stack only, rather than the
     * full thread "struct".  So shouldn't the THREAD_STRUCT_SIZE rather
     * be (thread_control_stack_size+BINDING_STACK_SIZE) instead?  That
     * would also do away with the LISP_FEATURE_SB_THREAD case.  Or does
     * it simply not matter?  --DFL */
    ptrdiff_t diff = ((char*)th->os_address)-(char*)addr;
    return diff > (ptrdiff_t)0 && diff < (ptrdiff_t)THREAD_STRUCT_SIZE
#ifdef LISP_FEATURE_SB_THREAD
        && addr != (os_vm_address_t) th->csp_around_foreign_call
#endif
        ;
}

static boolean
is_some_thread_local_addr(os_vm_address_t addr)
{
    boolean result = 0;
#ifdef LISP_FEATURE_SB_THREAD
    struct thread *th;
    pthread_mutex_lock(&all_threads_lock);
    for_each_thread(th) {
        if(is_thread_local_addr(th,addr)) {
            result = 1;
            break;
        }
    }
    pthread_mutex_unlock(&all_threads_lock);
#endif
    return result;
}


/* A tiny bit of interrupt.c state we want our paws on. */
extern boolean internal_errors_enabled;

extern void exception_handler_wrapper();

void
c_level_backtrace(const char* header, int depth)
{
    void* frame;
    int n = 0;
    void** lastseh;

    for (lastseh = get_seh_frame(); lastseh && (lastseh!=(void*)-1);
         lastseh = *lastseh);

    fprintf(stderr, "Backtrace: %s (thread %p)\n", header, this_thread);
    for (frame = __builtin_frame_address(0); frame; frame=*(void**)frame)
    {
        if ((n++)>depth)
            return;
        fprintf(stderr, "[#%02d]: ebp = 0x%p, ret = 0x%p\n",n,
                frame, ((void**)frame)[1]);
    }
}

#ifdef LISP_FEATURE_X86
#define voidreg(ctxptr,name) ((void*)((ctxptr)->E##name))
#else
#define voidreg(ctxptr,name) ((void*)((ctxptr)->R##name))
#endif


static int
handle_single_step(os_context_t *ctx)
{
    if (!single_stepping)
        return -1;

    /* We are doing a displaced instruction. At least function
     * end breakpoints use this. */
    restore_breakpoint_from_single_step(ctx);

    return 0;
}

#ifdef LISP_FEATURE_UD2_BREAKPOINTS
#define SBCL_EXCEPTION_BREAKPOINT EXCEPTION_ILLEGAL_INSTRUCTION
#define TRAP_CODE_WIDTH 2
#else
#define SBCL_EXCEPTION_BREAKPOINT EXCEPTION_BREAKPOINT
#define TRAP_CODE_WIDTH 1
#endif

static int
handle_breakpoint_trap(os_context_t *ctx, struct thread* self)
{
#ifdef LISP_FEATURE_UD2_BREAKPOINTS
    if (((unsigned short *)*os_context_pc_addr(ctx))[0] != 0x0b0f)
        return -1;
#endif

    /* Unlike some other operating systems, Win32 leaves EIP
     * pointing to the breakpoint instruction. */
    (*os_context_pc_addr(ctx)) += TRAP_CODE_WIDTH;

    /* Now EIP points just after the INT3 byte and aims at the
     * 'kind' value (eg trap_Cerror). */
    unsigned trap = *(unsigned char *)(*os_context_pc_addr(ctx));

#ifdef LISP_FEATURE_SB_THREAD
    /* Before any other trap handler: gc_safepoint ensures that
       inner alloc_sap for passing the context won't trap on
       pseudo-atomic. */
    if (trap == trap_PendingInterrupt) {
        /* Done everything needed for this trap, except EIP
           adjustment */
        arch_skip_instruction(ctx);
        thread_interrupted(ctx);
        return 0;
    }
#endif

    /* This is just for info in case the monitor wants to print an
     * approximation. */
    access_control_stack_pointer(self) =
        (lispobj *)*os_context_sp_addr(ctx);

    WITH_GC_AT_SAFEPOINTS_ONLY() {
#if defined(LISP_FEATURE_SB_THREAD)
        block_blockable_signals(0,&ctx->sigmask);
#endif
        handle_trap(ctx, trap);
#if defined(LISP_FEATURE_SB_THREAD)
        thread_sigmask(SIG_SETMASK,&ctx->sigmask,NULL);
#endif
    }

    /* Done, we're good to go! */
    return 0;
}

static int
handle_access_violation(os_context_t *ctx,
                        EXCEPTION_RECORD *exception_record,
                        void *fault_address,
                        struct thread* self)
{
    CONTEXT *win32_context = ctx->win32_context;

#if defined(LISP_FEATURE_X86)
    odxprint(pagefaults,
             "SEGV. ThSap %p, Eip %p, Esp %p, Esi %p, Edi %p, "
             "Addr %p Access %d\n",
             self,
             win32_context->Eip,
             win32_context->Esp,
             win32_context->Esi,
             win32_context->Edi,
             fault_address,
             exception_record->ExceptionInformation[0]);
#else
    odxprint(pagefaults,
             "SEGV. ThSap %p, Eip %p, Esp %p, Esi %p, Edi %p, "
             "Addr %p Access %d\n",
             self,
             win32_context->Rip,
             win32_context->Rsp,
             win32_context->Rsi,
             win32_context->Rdi,
             fault_address,
             exception_record->ExceptionInformation[0]);
#endif

    /* Stack: This case takes care of our various stack exhaustion
     * protect pages (with the notable exception of the control stack!). */
    if (self && local_thread_stack_address_p(fault_address)) {
        if (handle_guard_page_triggered(ctx, fault_address))
            return 0; /* gc safety? */
        goto try_recommit;
    }

    /* Safepoint pages */
#ifdef LISP_FEATURE_SB_THREAD
    if (fault_address == (void *) GC_SAFEPOINT_PAGE_ADDR) {
        thread_in_lisp_raised(ctx);
        return 0;
    }

    if ((((u64)fault_address) == ((u64)self->csp_around_foreign_call))){
        thread_in_safety_transition(ctx);
        return 0;
    }
#endif

    /* dynamic space */
    page_index_t index = find_page_index(fault_address);
    if (index != -1) {
        /*
         * Now, if the page is supposedly write-protected and this
         * is a write, tell the gc that it's been hit.
         */
        if (page_table[index].write_protected) {
            gencgc_handle_wp_violation(fault_address);
        } else {
            AVER(VirtualAlloc(PTR_ALIGN_DOWN(fault_address,os_vm_page_size),
                              os_vm_page_size,
                              MEM_COMMIT, PAGE_EXECUTE_READWRITE));
        }
        return 0;
    }

    if (fault_address == undefined_alien_address)
        return -1;

    /* linkage table or a "valid_lisp_addr" outside of dynamic space (?) */
    if (is_linkage_table_addr(fault_address)
        || is_valid_lisp_addr(fault_address))
        goto try_recommit;

    return -1;

try_recommit:
    /* First use of a new page, lets get some memory for it. */

#if defined(LISP_FEATURE_X86)
    AVER(VirtualAlloc(PTR_ALIGN_DOWN(fault_address,os_vm_page_size),
                      os_vm_page_size,
                      MEM_COMMIT, PAGE_EXECUTE_READWRITE)
         ||(fprintf(stderr,"Unable to recommit addr %p eip 0x%08lx\n",
                    fault_address, win32_context->Eip) &&
            (c_level_backtrace("BT",5),
             fake_foreign_function_call(ctx),
             lose("Lispy backtrace"),
             0)));
#else
    AVER(VirtualAlloc(PTR_ALIGN_DOWN(fault_address,os_vm_page_size),
                      os_vm_page_size,
                      MEM_COMMIT, PAGE_EXECUTE_READWRITE)
         ||(fprintf(stderr,"Unable to recommit addr %p eip 0x%p\n",
                    fault_address, (void*)win32_context->Rip) &&
            (c_level_backtrace("BT",5),
             fake_foreign_function_call(ctx),
             lose("Lispy backtrace"),
             0)));
#endif

    return 0;
}

static void
signal_internal_error_or_lose(os_context_t *ctx,
                              EXCEPTION_RECORD *exception_record,
                              void *fault_address)
{
    /*
     * If we fall through to here then we need to either forward
     * the exception to the lisp-side exception handler if it's
     * set up, or drop to LDB.
     */

    if (internal_errors_enabled) {
        lispobj context_sap;
        lispobj exception_record_sap;

        asm("fnclex");
        /* We're making the somewhat arbitrary decision that having
         * internal errors enabled means that lisp has sufficient
         * marbles to be able to handle exceptions, but exceptions
         * aren't supposed to happen during cold init or reinit
         * anyway. */

#if defined(LISP_FEATURE_SB_THREAD)
        block_blockable_signals(0,&ctx->sigmask);
#endif
        fake_foreign_function_call(ctx);

        WITH_GC_AT_SAFEPOINTS_ONLY() {
            /* Allocate the SAP objects while the "interrupts" are still
             * disabled. */
            context_sap = alloc_sap(ctx);
            exception_record_sap = alloc_sap(exception_record);
#if defined(LISP_FEATURE_SB_THREAD)
            thread_sigmask(SIG_SETMASK, &ctx->sigmask, NULL);
#endif

            /* The exception system doesn't automatically clear pending
             * exceptions, so we lose as soon as we execute any FP
             * instruction unless we do this first. */
            /* Call into lisp to handle things. */
            funcall2(StaticSymbolFunction(HANDLE_WIN32_EXCEPTION),
                     context_sap,
                     exception_record_sap);
        }
        /* If Lisp doesn't nlx, we need to put things back. */
        undo_fake_foreign_function_call(ctx);
#if defined(LISP_FEATURE_SB_THREAD)
        thread_sigmask(SIG_SETMASK, &ctx->sigmask, NULL);
#endif
        /* FIXME: HANDLE-WIN32-EXCEPTION should be allowed to decline */
        return;
    }

    fprintf(stderr, "Exception Code: 0x%p.\n",
            (void*)(intptr_t)exception_record->ExceptionCode);
    fprintf(stderr, "Faulting IP: 0x%p.\n",
            (void*)(intptr_t)exception_record->ExceptionAddress);
    if (exception_record->ExceptionCode == EXCEPTION_ACCESS_VIOLATION) {
        MEMORY_BASIC_INFORMATION mem_info;

        if (VirtualQuery(fault_address, &mem_info, sizeof mem_info)) {
            fprintf(stderr, "page status: 0x%lx.\n", mem_info.State);
        }

        fprintf(stderr, "Was writing: %p, where: 0x%p.\n",
                (void*)exception_record->ExceptionInformation[0],
                fault_address);
    }

    fflush(stderr);

    fake_foreign_function_call(ctx);
    lose("Exception too early in cold init, cannot continue.");
}

/*
 * A good explanation of the exception handling semantics is
 *   http://win32assembly.online.fr/Exceptionhandling.html (possibly defunct)
 * or:
 *   http://www.microsoft.com/msj/0197/exception/exception.aspx
 */

EXCEPTION_DISPOSITION
handle_exception(EXCEPTION_RECORD *exception_record,
                 struct lisp_exception_frame *exception_frame,
                 CONTEXT *win32_context,
                 void *dispatcher_context)
{
    if (!win32_context)
        /* Not certain why this should be possible, but let's be safe... */
        return ExceptionContinueSearch;

    if (exception_record->ExceptionFlags & (EH_UNWINDING | EH_EXIT_UNWIND)) {
        /* If we're being unwound, be graceful about it. */

        /* Undo any dynamic bindings. */
        unbind_to_here(exception_frame->bindstack_pointer,
                       arch_os_get_current_thread());
        return ExceptionContinueSearch;
    }

    DWORD lastError = GetLastError();
    DWORD lastErrno = errno;
    DWORD code = exception_record->ExceptionCode;
    struct thread* self = arch_os_get_current_thread();

    os_context_t context, *ctx = &context;
    context.win32_context = win32_context;
#if defined(LISP_FEATURE_SB_THREAD)
    context.sigmask = self ? self->os_thread->blocked_signal_set : 0;
#endif

    os_context_register_t oldbp = NULL;
    if (self) {
        oldbp = self ? self->carried_base_pointer : 0;
        self->carried_base_pointer
            = (os_context_register_t) voidreg(win32_context, bp);
    }

    /* For EXCEPTION_ACCESS_VIOLATION only. */
    void *fault_address = (void *)exception_record->ExceptionInformation[1];

    odxprint(seh,
             "SEH: rec %p, ctxptr %p, rip %p, fault %p\n"
             "... code %p, rcx %p, fp-tags %p\n\n",
             exception_record,
             win32_context,
             voidreg(win32_context,ip),
             fault_address,
             (void*)(intptr_t)code,
             voidreg(win32_context,cx),
             win32_context->FloatSave.TagWord);

    /* This function had become unwieldy.  Let's cut it down into
     * pieces based on the different exception codes.  Each exception
     * code handler gets the chance to decline by returning non-zero if it
     * isn't happy: */

    int rc;
    switch (code) {
    case EXCEPTION_ACCESS_VIOLATION:
        rc = handle_access_violation(
            ctx, exception_record, fault_address, self);
        break;

    case SBCL_EXCEPTION_BREAKPOINT:
        rc = handle_breakpoint_trap(ctx, self);
        break;

    case EXCEPTION_SINGLE_STEP:
        rc = handle_single_step(ctx);
        break;

    default:
        rc = -1;
    }

    if (rc)
        /* All else failed, drop through to the lisp-side exception handler. */
        signal_internal_error_or_lose(ctx, exception_record, fault_address);

    if (self)
        self->carried_base_pointer = oldbp;

    errno = lastErrno;
    SetLastError(lastError);
    return ExceptionContinueExecution;
}

#ifdef LISP_FEATURE_X86_64

#define RESTORING_ERRNO()                                       \
    int sbcl__lastErrno = errno;                                \
    RUN_BODY_ONCE(restoring_errno, errno = sbcl__lastErrno)

LONG
veh(EXCEPTION_POINTERS *ep)
{
    EXCEPTION_DISPOSITION disp;

    RESTORING_ERRNO() {
        if (!pthread_self())
            return EXCEPTION_CONTINUE_SEARCH;
    }

    disp = handle_exception(ep->ExceptionRecord,0,ep->ContextRecord,0);

    switch (disp)
    {
    case ExceptionContinueExecution:
        return EXCEPTION_CONTINUE_EXECUTION;
    case ExceptionContinueSearch:
        return EXCEPTION_CONTINUE_SEARCH;
    default:
        fprintf(stderr,"Exception handler is mad\n");
        ExitProcess(0);
    }
}
#endif

os_context_register_t
carry_frame_pointer(os_context_register_t default_value)
{
    struct thread* self = arch_os_get_current_thread();
    os_context_register_t bp = self->carried_base_pointer;
    return bp ? bp : default_value;
}

void
wos_install_interrupt_handlers(struct lisp_exception_frame *handler)
{
#ifdef LISP_FEATURE_X86
    handler->next_frame = get_seh_frame();
    handler->handler = (void*)exception_handler_wrapper;
    set_seh_frame(handler);
#else
    static int once = 0;
    if (!once++)
        AddVectoredExceptionHandler(1,veh);
#endif
}

/*
 * The stubs below are replacements for the windows versions,
 * which can -fail- when used in our memory spaces because they
 * validate the memory spaces they are passed in a way that
 * denies our exception handler a chance to run.
 */

void *memmove(void *dest, const void *src, size_t n)
{
    if (dest < src) {
        int i;
        for (i = 0; i < n; i++) *(((char *)dest)+i) = *(((char *)src)+i);
    } else {
        while (n--) *(((char *)dest)+n) = *(((char *)src)+n);
    }
    return dest;
}

void *memcpy(void *dest, const void *src, size_t n)
{
    while (n--) *(((char *)dest)+n) = *(((char *)src)+n);
    return dest;
}

char *dirname(char *path)
{
    static char buf[PATH_MAX + 1];
    size_t pathlen = strlen(path);
    int i;

    if (pathlen >= sizeof(buf)) {
        lose("Pathname too long in dirname.\n");
        return NULL;
    }

    strcpy(buf, path);
    for (i = pathlen; i >= 0; --i) {
        if (buf[i] == '/' || buf[i] == '\\') {
            buf[i] = '\0';
            break;
        }
    }

    return buf;
}

// 0 - not a socket or other error, 1 - has input, 2 - has no input
int
socket_input_available(HANDLE socket)
{
    unsigned long count = 0, count_size = 0;
    int wsaErrno = GetLastError();
    int err = WSAIoctl((SOCKET)socket, FIONREAD, NULL, 0,
                       &count, sizeof(count), &count_size, NULL, NULL);

    int ret;

    if (err == 0) {
        ret = (count > 0) ? 1 : 2;
    } else
        ret = 0;
    SetLastError(wsaErrno);
    return ret;
}

/* Unofficial but widely used property of console handles: they have
   #b11 in two minor bits, opposed to other handles, that are
   machine-word-aligned. Properly emulated even on wine.

   Console handles are special in many aspects, e.g. they aren't NTDLL
   system handles: kernel32 redirects console operations to CSRSS
   requests. Using the hack below to distinguish console handles is
   justified, as it's the only method that won't hang during
   outstanding reads, won't try to lock NT kernel object (if there is
   one; console isn't), etc. */
int
console_handle_p(HANDLE handle)
{
    return (handle != NULL)&&
        (handle != INVALID_HANDLE_VALUE)&&
        ((((int)(intptr_t)handle)&3)==3);
}

/* Atomically mark current thread as (probably) doing synchronous I/O
 * on handle, if no cancellation is requested yet (and return TRUE),
 * otherwise clear thread's I/O cancellation flag and return false.
 */
static
boolean io_begin_interruptible(HANDLE handle)
{
    /* No point in doing it unless OS supports cancellation from other
     * threads */
    if (!ptr_CancelIoEx)
        return 1;

    if (!__sync_bool_compare_and_swap(&this_thread->synchronous_io_handle_and_flag,
                                      0, handle)) {
        ResetEvent(this_thread->private_events.events[0]);
        this_thread->synchronous_io_handle_and_flag = 0;
        return 0;
    }
    return 1;
}

static pthread_mutex_t interrupt_io_lock = PTHREAD_MUTEX_INITIALIZER;

/* Unmark current thread as (probably) doing synchronous I/O; if an
 * I/O cancellation was requested, postpone it until next
 * io_begin_interruptible */
static void
io_end_interruptible(HANDLE handle)
{
    if (!ptr_CancelIoEx)
        return;
    pthread_mutex_lock(&interrupt_io_lock);
    __sync_bool_compare_and_swap(&this_thread->synchronous_io_handle_and_flag,
                                 handle, 0);
    pthread_mutex_unlock(&interrupt_io_lock);
}

/* Documented limit for ReadConsole/WriteConsole is 64K bytes.
   Real limit observed on W2K-SP3 is somewhere in between 32KiB and 64Kib...
*/
#define MAX_CONSOLE_TCHARS 16384

int
win32_write_unicode_console(HANDLE handle, void * buf, int count)
{
    DWORD written = 0;
    DWORD nchars;
    BOOL result;
    nchars = count>>1;
    if (nchars>MAX_CONSOLE_TCHARS) nchars = MAX_CONSOLE_TCHARS;

    if (!io_begin_interruptible(handle)) {
        errno = EINTR;
        return -1;
    }
    result = WriteConsoleW(handle,buf,nchars,&written,NULL);
    io_end_interruptible(handle);

    if (result) {
        if (!written) {
            errno = EINTR;
            return -1;
        } else {
            return 2*written;
        }
    } else {
        DWORD err = GetLastError();
        odxprint(io,"WriteConsole fails => %u\n", err);
        errno = (err==ERROR_OPERATION_ABORTED ? EINTR : EIO);
        return -1;
    }
}

/*
 * (AK writes:)
 *
 * It may be unobvious, but (probably) the most straightforward way of
 * providing some sane CL:LISTEN semantics for line-mode console
 * channel requires _dedicated input thread_.
 *
 * LISTEN should return true iff the next (READ-CHAR) won't have to
 * wait. As our console may be shared with another process, entirely
 * out of our control, looking at the events in PeekConsoleEvent
 * result (and searching for #\Return) doesn't cut it.
 *
 * We decided that console input thread must do something smarter than
 * a bare loop of continuous ReadConsoleW(). On Unix, user experience
 * with the terminal is entirely unaffected by the fact that some
 * process does (or doesn't) call read(); the situation on MS Windows
 * is different.
 *
 * Echo output and line editing present on MS Windows while some
 * process is waiting in ReadConsole(); otherwise all input events are
 * buffered. If our thread were calling ReadConsole() all the time, it
 * would feel like Unix cooked mode.
 *
 * But we don't write a Unix emulator here, even if it sometimes feels
 * like that; therefore preserving this aspect of console I/O seems a
 * good thing to us.
 *
 * LISTEN itself becomes trivial with dedicated input thread, but the
 * goal stated above -- provide `native' user experience with blocked
 * console -- don't play well with this trivial implementation.
 *
 * What's currently implemented is a compromise, looking as something
 * in between Unix cooked mode and Win32 line mode.
 *
 * 1. As long as no console I/O function is called (incl. CL:LISTEN),
 * console looks `blocked': no echo, no line editing.
 *
 * 2. (READ-CHAR), (READ-SEQUENCE) and other functions doing real
 * input result in the ReadConsole request (in a dedicated thread);
 *
 * 3. Once ReadConsole is called, it is not cancelled in the
 * middle. In line mode, it returns when <Enter> key is hit (or
 * something like that happens). Therefore, if line editing and echo
 * output had a chance to happen, console won't look `blocked' until
 * the line is entered (even if line input was triggered by
 * (READ-CHAR)).
 *
 * 4. LISTEN may request ReadConsole too (if no other thread is
 * reading the console and no data are queued). It's the only case
 * when the console becomes `unblocked' without any actual input
 * requested by Lisp code.  LISTEN check if there is at least one
 * input event in PeekConsole queue; unless there is such an event,
 * ReadConsole is not triggered by LISTEN.
 *
 * 5. Console-reading Lisp thread now may be interrupted immediately;
 * ReadConsole call itself, however, continues until the line is
 * entered.
 */

struct {
    WCHAR buffer[MAX_CONSOLE_TCHARS];
    DWORD head, tail;
    pthread_mutex_t lock;
    pthread_cond_t cond_has_data;
    pthread_cond_t cond_has_client;
    pthread_t thread;
    boolean initialized;
    HANDLE handle;
    boolean in_progress;
} ttyinput = {.lock = PTHREAD_MUTEX_INITIALIZER};

static void*
tty_read_line_server()
{
    pthread_mutex_lock(&ttyinput.lock);
    while (ttyinput.handle) {
        DWORD nchars;
        BOOL ok;

        while (!ttyinput.in_progress)
            pthread_cond_wait(&ttyinput.cond_has_client,&ttyinput.lock);

        pthread_mutex_unlock(&ttyinput.lock);

        ok = ReadConsoleW(ttyinput.handle,
                          &ttyinput.buffer[ttyinput.tail],
                          MAX_CONSOLE_TCHARS-ttyinput.tail,
                          &nchars,NULL);

        pthread_mutex_lock(&ttyinput.lock);

        if (ok) {
            ttyinput.tail += nchars;
            pthread_cond_broadcast(&ttyinput.cond_has_data);
        }
        ttyinput.in_progress = 0;
    }
    pthread_mutex_unlock(&ttyinput.lock);
    return NULL;
}

static boolean
tty_maybe_initialize_unlocked(HANDLE handle)
{
    if (!ttyinput.initialized) {
        if (!DuplicateHandle(GetCurrentProcess(),handle,
                             GetCurrentProcess(),&ttyinput.handle,
                             0,FALSE,DUPLICATE_SAME_ACCESS)) {
            return 0;
        }
        pthread_cond_init(&ttyinput.cond_has_data,NULL);
        pthread_cond_init(&ttyinput.cond_has_client,NULL);
        pthread_create(&ttyinput.thread,NULL,tty_read_line_server,NULL);
        ttyinput.initialized = 1;
    }
    return 1;
}

boolean
win32_tty_listen(HANDLE handle)
{
    boolean result = 0;
    INPUT_RECORD ir;
    DWORD nevents;
    pthread_mutex_lock(&ttyinput.lock);
    if (!tty_maybe_initialize_unlocked(handle))
        result = 0;

    if (ttyinput.in_progress) {
        result = 0;
    } else {
        if (ttyinput.head != ttyinput.tail) {
            result = 1;
        } else {
            if (PeekConsoleInput(ttyinput.handle,&ir,1,&nevents) && nevents) {
                ttyinput.in_progress = 1;
                pthread_cond_broadcast(&ttyinput.cond_has_client);
            }
        }
    }
    pthread_mutex_unlock(&ttyinput.lock);
    return result;
}

static int
tty_read_line_client(HANDLE handle, void* buf, int count)
{
    int result = 0;
    int nchars = count / sizeof(WCHAR);
    sigset_t pendset;

    if (!nchars)
        return 0;
    if (nchars>MAX_CONSOLE_TCHARS)
        nchars=MAX_CONSOLE_TCHARS;

    count = nchars*sizeof(WCHAR);

    pthread_mutex_lock(&ttyinput.lock);

    if (!tty_maybe_initialize_unlocked(handle)) {
        result = -1;
        errno = EIO;
        goto unlock;
    }

    while (!result) {
        while (ttyinput.head == ttyinput.tail) {
            if (!io_begin_interruptible(ttyinput.handle)) {
                ttyinput.in_progress = 0;
                result = -1;
                errno = EINTR;
                goto unlock;
            } else {
                if (!ttyinput.in_progress) {
                    /* We are to wait */
                    ttyinput.in_progress=1;
                    /* wake console reader */
                    pthread_cond_broadcast(&ttyinput.cond_has_client);
                }
                pthread_cond_wait(&ttyinput.cond_has_data, &ttyinput.lock);
                io_end_interruptible(ttyinput.handle);
            }
        }
        result = sizeof(WCHAR)*(ttyinput.tail-ttyinput.head);
        if (result > count) {
            result = count;
        }
        if (result) {
            if (result > 0) {
                DWORD nch,offset = 0;
                LPWSTR ubuf = buf;

                memcpy(buf,&ttyinput.buffer[ttyinput.head],count);
                ttyinput.head += (result / sizeof(WCHAR));
                if (ttyinput.head == ttyinput.tail)
                    ttyinput.head = ttyinput.tail = 0;

                for (nch=0;nch<result/sizeof(WCHAR);++nch) {
                    if (ubuf[nch]==13) {
                        ++offset;
                    } else {
                        ubuf[nch-offset]=ubuf[nch];
                    }
                }
                result-=offset*sizeof(WCHAR);

            }
        } else {
            result = -1;
            ttyinput.head = ttyinput.tail = 0;
            errno = EIO;
        }
    }
unlock:
    pthread_mutex_unlock(&ttyinput.lock);
    return result;
}

int
win32_read_unicode_console(HANDLE handle, void* buf, int count)
{

    int result;
    result = tty_read_line_client(handle,buf,count);
    return result;
}

boolean
win32_maybe_interrupt_io(void* thread)
{
    struct thread *th = thread;
    boolean done = 0;
    if (ptr_CancelIoEx) {
        pthread_mutex_lock(&interrupt_io_lock);
        HANDLE h = (HANDLE)
            InterlockedExchangePointer((volatile LPVOID *)
                                       &th->synchronous_io_handle_and_flag,
                                       (LPVOID)INVALID_HANDLE_VALUE);
        if (h && (h!=INVALID_HANDLE_VALUE)) {
            if (console_handle_p(h)) {
                pthread_mutex_lock(&ttyinput.lock);
                pthread_cond_broadcast(&ttyinput.cond_has_data);
                pthread_mutex_unlock(&ttyinput.lock);
            }
            if (ptr_CancelSynchronousIo) {
                pthread_mutex_lock(&th->os_thread->fiber_lock);
                done = !!ptr_CancelSynchronousIo(th->os_thread->fiber_group->handle);
                pthread_mutex_unlock(&th->os_thread->fiber_lock);
            }
            done |= !!ptr_CancelIoEx(h,NULL);
        }
        pthread_mutex_unlock(&interrupt_io_lock);
    }
    return done;
}

static const LARGE_INTEGER zero_large_offset = {.QuadPart = 0LL};

int
win32_unix_write(HANDLE handle, void * buf, int count)
{
    DWORD written_bytes;
    OVERLAPPED overlapped;
    struct thread * self = arch_os_get_current_thread();
    BOOL waitInGOR;
    LARGE_INTEGER file_position;
    BOOL seekable;
    BOOL ok;

    if (console_handle_p(handle))
        return win32_write_unicode_console(handle,buf,count);

    overlapped.hEvent = self->private_events.events[0];
    seekable = SetFilePointerEx(handle,
                                zero_large_offset,
                                &file_position,
                                FILE_CURRENT);
    if (seekable) {
        overlapped.Offset = file_position.LowPart;
        overlapped.OffsetHigh = file_position.HighPart;
    } else {
        overlapped.Offset = 0;
        overlapped.OffsetHigh = 0;
    }
    if (!io_begin_interruptible(handle)) {
        errno = EINTR;
        return -1;
    }
    ok = WriteFile(handle, buf, count, &written_bytes, &overlapped);
    io_end_interruptible(handle);

    if (ok) {
        goto done_something;
    } else {
        DWORD errorCode = GetLastError();
        if (errorCode==ERROR_OPERATION_ABORTED) {
            GetOverlappedResult(handle,&overlapped,&written_bytes,FALSE);
            errno = EINTR;
            return -1;
        }
        if (errorCode!=ERROR_IO_PENDING) {
            errno = EIO;
            return -1;
        } else {
            if(WaitForMultipleObjects(2,self->private_events.events,
                                      FALSE,INFINITE) != WAIT_OBJECT_0) {
                CancelIo(handle);
                waitInGOR = TRUE;
            } else {
                waitInGOR = FALSE;
            }
            if (!GetOverlappedResult(handle,&overlapped,&written_bytes,waitInGOR)) {
                if (GetLastError()==ERROR_OPERATION_ABORTED) {
                    errno = EINTR;
                } else {
                    errno = EIO;
                }
                return -1;
            } else {
                goto done_something;
            }
        }
    }
  done_something:
    if (seekable) {
        file_position.QuadPart += written_bytes;
        SetFilePointerEx(handle,file_position,NULL,FILE_BEGIN);
    }
    return written_bytes;
}

int
win32_unix_read(HANDLE handle, void * buf, int count)
{
    OVERLAPPED overlapped = {.Internal=0};
    DWORD read_bytes = 0;
    struct thread * self = arch_os_get_current_thread();
    DWORD errorCode = 0;
    BOOL waitInGOR = FALSE;
    BOOL ok = FALSE;
    LARGE_INTEGER file_position;
    BOOL seekable;

    if (console_handle_p(handle))
        return win32_read_unicode_console(handle,buf,count);

    overlapped.hEvent = self->private_events.events[0];
    /* If it has a position, we won't try overlapped */
    seekable = SetFilePointerEx(handle,
                                zero_large_offset,
                                &file_position,
                                FILE_CURRENT);
    if (seekable) {
        overlapped.Offset = file_position.LowPart;
        overlapped.OffsetHigh = file_position.HighPart;
    } else {
        overlapped.Offset = 0;
        overlapped.OffsetHigh = 0;
    }
    if (!io_begin_interruptible(handle)) {
        errno = EINTR;
        return -1;
    }
    ok = ReadFile(handle,buf,count,&read_bytes, &overlapped);
    io_end_interruptible(handle);
    if (ok) {
        /* immediately */
        goto done_something;
    } else {
        errorCode = GetLastError();
        if (errorCode == ERROR_HANDLE_EOF ||
            errorCode == ERROR_BROKEN_PIPE ||
            errorCode == ERROR_NETNAME_DELETED) {
            read_bytes = 0;
            goto done_something;
        }
        if (errorCode==ERROR_OPERATION_ABORTED) {
            GetOverlappedResult(handle,&overlapped,&read_bytes,FALSE);
            errno = EINTR;
            return -1;
        }
        if (errorCode!=ERROR_IO_PENDING) {
            /* is it some _real_ error? */
            errno = EIO;
            return -1;
        } else {
            int ret;
            if( (ret = WaitForMultipleObjects(2,self->private_events.events,
                                              FALSE,INFINITE)) != WAIT_OBJECT_0) {
                CancelIo(handle);
                waitInGOR = TRUE;
                /* Waiting for IO only */
            } else {
                waitInGOR = FALSE;
            }
            ok = GetOverlappedResult(handle,&overlapped,&read_bytes,waitInGOR);
            if (!ok) {
                errorCode = GetLastError();
                if (errorCode == ERROR_HANDLE_EOF ||
                    errorCode == ERROR_BROKEN_PIPE ||
                    errorCode == ERROR_NETNAME_DELETED) {
                    read_bytes = 0;
                    goto done_something;
                } else {
                    if (errorCode == ERROR_OPERATION_ABORTED)
                        errno = EINTR;      /* that's it. */
                    else
                        errno = EIO;        /* something unspecific */
                    return -1;
                }
            } else
                goto done_something;
        }
    }
  done_something:
    if (seekable) {
        file_position.QuadPart += read_bytes;
        SetFilePointerEx(handle,file_position,NULL,FILE_BEGIN);
    }
    return read_bytes;
}

/* We used to have a scratch() function listing all symbols needed by
 * Lisp.  Much rejoicing commenced upon its removal.  However, I would
 * like cold init to fail aggressively when encountering unused symbols.
 * That poses a problem, however, since our C code no longer includes
 * any references to symbols in ws2_32.dll, and hence the linker
 * completely ignores our request to reference it (--no-as-needed does
 * not work).  Warm init would later load the DLLs explicitly, but then
 * it's too late for an early sanity check.  In the unfortunate spirit
 * of scratch(), continue to reference some required DLLs explicitly by
 * means of one scratch symbol per DLL.
 */
void scratch(void)
{
    /* a function from ws2_32.dll */
    shutdown(0, 0);

    /* a function from shell32.dll */
    SHGetFolderPathA(0, 0, 0, 0, 0);

    /* from advapi32.dll */
    CryptGenRandom(0, 0, 0);
}

char *
os_get_runtime_executable_path(int external)
{
    char path[MAX_PATH + 1];
    DWORD bufsize = sizeof(path);
    DWORD size;

    if ((size = GetModuleFileNameA(NULL, path, bufsize)) == 0)
        return NULL;
    else if (size == bufsize && GetLastError() == ERROR_INSUFFICIENT_BUFFER)
        return NULL;

    return copied_string(path);
}

#ifdef LISP_FEATURE_SB_THREAD

int
win32_wait_object_or_signal(HANDLE waitFor)
{
    struct thread * self = arch_os_get_current_thread();
    HANDLE handles[2];
    handles[0] = waitFor;
    handles[1] = self->private_events.events[1];
    return
        WaitForMultipleObjects(2,handles, FALSE,INFINITE);
}

/*
 * Portability glue for win32 waitable timers.
 *
 * One may ask: Why is there a wrapper in C when the calls are so
 * obvious that Lisp could do them directly (as it did on Windows)?
 *
 * But the answer is that on POSIX platforms, we now emulate the win32
 * calls and hide that emulation behind this os_* abstraction.
 */
HANDLE
os_create_wtimer()
{
    return CreateWaitableTimer(0, 0, 0);
}

int
os_wait_for_wtimer(HANDLE handle)
{
    return win32_wait_object_or_signal(handle);
}

void
os_close_wtimer(HANDLE handle)
{
    CloseHandle(handle);
}

void
os_set_wtimer(HANDLE handle, int sec, int nsec)
{
    /* in units of 100ns, i.e. 0.1us. Negative for relative semantics. */
    long long dueTime
        = -(((long long) sec) * 10000000
            + ((long long) nsec + 99) / 100);
    SetWaitableTimer(handle, (LARGE_INTEGER*) &dueTime, 0, 0, 0, 0);
}

void
os_cancel_wtimer(HANDLE handle)
{
    CancelWaitableTimer(handle);
}
#endif

/* EOF */
