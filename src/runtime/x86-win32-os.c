/*
 * The x86 Win32 incarnation of arch-dependent OS-dependent routines.
 * See also "win32-os.c".
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

#include <stdio.h>
#include <stddef.h>
#include <sys/param.h>
#include <sys/file.h>
#include <sys/types.h>
#include <unistd.h>
#include <errno.h>

#include "os.h"
#include "arch.h"
#include "globals.h"
#include "interrupt.h"
#include "interr.h"
#include "lispregs.h"
#include "sbcl.h"

#include <sys/types.h>
#include "runtime.h"
#include <sys/time.h>
#include <sys/stat.h>
#include <unistd.h>
#include "thread.h"             /* dynamic_values_bytes */
#include "cpputil.h"            /* PTR_ALIGN... */

#include "validate.h"

int arch_os_thread_init(struct thread *thread)
{
    {
        void *top_exception_frame;
        void *cur_stack_end;
        void *cur_stack_start;
        MEMORY_BASIC_INFORMATION stack_memory;

        asm volatile ("movl %%fs:0,%0": "=r" (top_exception_frame));
        asm volatile ("movl %%fs:4,%0": "=r" (cur_stack_end));

        /* Can't pull stack start from fs:4 or fs:8 or whatever,
         * because that's only what currently has memory behind
         * it from being used, so do a quick VirtualQuery() and
         * grab the AllocationBase. -AB 2006/11/25
         */

        if (!VirtualQuery(&stack_memory, &stack_memory, sizeof(stack_memory))) {
            fprintf(stderr, "VirtualQuery: 0x%lx.\n", GetLastError());
            lose("Could not query stack memory information.");
        }

        cur_stack_start = stack_memory.AllocationBase
            /* Kludge: Elide SBCL's guard page from the range.  (The
             * real solution is to not establish SBCL's guard page in
             * the first place.  The trick will be to find a good time
             * at which to re-enable the Windows guard page when
             * returning from it though.) */
            + os_vm_page_size;

        /* We use top_exception_frame rather than cur_stack_end to
         * elide the last few (boring) stack entries at the bottom of
         * the backtrace.
         */
        thread->control_stack_start = cur_stack_start;
        thread->control_stack_end = top_exception_frame;

#ifndef LISP_FEATURE_SB_THREAD
        /*
         * Theoretically, threaded SBCL binds directly against
         * the thread structure for these values. We don't do
         * threads yet, but we'll probably do the same. We do
         * need to reset these, though, because they were
         * initialized based on the wrong stack space.
         */
        SetSymbolValue(CONTROL_STACK_START,(lispobj)thread->control_stack_start,thread);
        SetSymbolValue(CONTROL_STACK_END,(lispobj)thread->control_stack_end,thread);
#endif
    }

#ifdef LISP_FEATURE_SB_THREAD
    TlsSetValue(OUR_TLS_INDEX,thread);
#endif
    return 1;
}

/* free any arch/os-specific resources used by thread, which is now
 * defunct.  Not called on live threads
 */

int arch_os_thread_cleanup(struct thread *thread) {
    return 0;
}

#if defined(LISP_FEATURE_SB_THREAD)
sigset_t *os_context_sigmask_addr(os_context_t *context)
{
  return &context->sigmask;
}
#endif

os_context_register_t *
os_context_register_addr(os_context_t *context, int offset)
{
    static const size_t offsets[8] = {
        offsetof(CONTEXT,Eax),
        offsetof(CONTEXT,Ecx),
        offsetof(CONTEXT,Edx),
        offsetof(CONTEXT,Ebx),
        offsetof(CONTEXT,Esp),
        offsetof(CONTEXT,Ebp),
        offsetof(CONTEXT,Esi),
        offsetof(CONTEXT,Edi),
    };
    return
        (offset >= 0 && offset < 16) ?
        ((void*)(context->win32_context)) + offsets[offset>>1]  : 0;
}

os_context_register_t *
os_context_pc_addr(os_context_t *context)
{
    return (void*)&context->win32_context->Eip; /*  REG_EIP */
}

os_context_register_t *
os_context_sp_addr(os_context_t *context)
{
    return (void*)&context->win32_context->Esp; /* REG_UESP */
}

os_context_register_t *
os_context_fp_addr(os_context_t *context)
{
    return (void*)&context->win32_context->Ebp; /* REG_EBP */
}

unsigned long
os_context_fp_control(os_context_t *context)
{
    return ((((context->win32_context->FloatSave.ControlWord) & 0xffff) ^ 0x3f) |
            (((context->win32_context->FloatSave.StatusWord) & 0xffff) << 16));
}

void
os_restore_fp_control(os_context_t *context)
{
    asm ("fldcw %0" : : "m" (context->win32_context->FloatSave.ControlWord));
}

void
os_flush_icache(os_vm_address_t address, os_vm_size_t length)
{
}
