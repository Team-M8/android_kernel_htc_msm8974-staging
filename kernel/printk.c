/*
 *  linux/kernel/printk.c
 *
 *  Copyright (C) 1991, 1992  Linus Torvalds
 *
 * Modified to make sys_syslog() more flexible: added commands to
 * return the last 4k of kernel messages, regardless of whether
 * they've been read or not.  Added option to suppress kernel printk's
 * to the console.  Added hook for sending the console messages
 * elsewhere, in preparation for a serial line console (someday).
 * Ted Ts'o, 2/11/93.
 * Modified for sysctl support, 1/8/97, Chris Horn.
 * Fixed SMP synchronization, 08/08/99, Manfred Spraul
 *     manfred@colorfullife.com
 * Rewrote bits to get rid of console_lock
 *	01Mar01 Andrew Morton
 */

#include <linux/kernel.h>
#include <linux/mm.h>
#include <linux/tty.h>
#include <linux/tty_driver.h>
#include <linux/console.h>
#include <linux/init.h>
#include <linux/jiffies.h>
#include <linux/nmi.h>
#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/interrupt.h>			
#include <linux/delay.h>
#include <linux/smp.h>
#include <linux/security.h>
#include <linux/bootmem.h>
#include <linux/memblock.h>
#include <linux/syscalls.h>
#include <linux/kexec.h>
#include <linux/kdb.h>
#include <linux/ratelimit.h>
#include <linux/kmsg_dump.h>
#include <linux/syslog.h>
#include <linux/cpu.h>
#include <linux/notifier.h>
#include <linux/rculist.h>

#include <asm/uaccess.h>

#include <mach/msm_rtb.h>
#define CREATE_TRACE_POINTS
#include <trace/events/printk.h>

void asmlinkage __attribute__((weak)) early_printk(const char *fmt, ...)
{
}

/* printk's without a loglevel use this.. */
#define DEFAULT_MESSAGE_LOGLEVEL CONFIG_DEFAULT_MESSAGE_LOGLEVEL

#define MINIMUM_CONSOLE_LOGLEVEL 1 
#define DEFAULT_CONSOLE_LOGLEVEL 7 

DECLARE_WAIT_QUEUE_HEAD(log_wait);

int console_printk[4] = {
	DEFAULT_CONSOLE_LOGLEVEL,	
	DEFAULT_MESSAGE_LOGLEVEL,	
	MINIMUM_CONSOLE_LOGLEVEL,	
	DEFAULT_CONSOLE_LOGLEVEL,	
};

int oops_in_progress;
EXPORT_SYMBOL(oops_in_progress);

static DEFINE_SEMAPHORE(console_sem);
struct console *console_drivers;
EXPORT_SYMBOL_GPL(console_drivers);

static int console_locked, console_suspended;

static struct console *exclusive_console;

struct console_cmdline
{
	char	name[16];			/* Name of the driver	    */
	int	index;				/* Minor dev. to use	    */
	char	*options;			/* Options for the driver   */
#ifdef CONFIG_A11Y_BRAILLE_CONSOLE
	char	*brl_options;			
#endif
};

#define MAX_CMDLINECONSOLES 8

static struct console_cmdline console_cmdline[MAX_CMDLINECONSOLES];
static int selected_console = -1;
static int preferred_console = -1;
int console_set_on_cmdline;
EXPORT_SYMBOL(console_set_on_cmdline);

static int console_may_schedule;

#ifdef CONFIG_PRINTK
/*
 * The printk log buffer consists of a chain of concatenated variable
 * length records. Every record starts with a record header, containing
 * the overall length of the record.
 *
 * The heads to the first and last entry in the buffer, as well as the
 * sequence numbers of these both entries are maintained when messages
 * are stored..
 *
 * If the heads indicate available messages, the length in the header
 * tells the start next message. A length == 0 for the next message
 * indicates a wrap-around to the beginning of the buffer.
 *
 * Every record carries the monotonic timestamp in microseconds, as well as
 * the standard userspace syslog level and syslog facility. The usual
 * kernel messages use LOG_KERN; userspace-injected messages always carry
 * a matching syslog facility, by default LOG_USER. The origin of every
 * message can be reliably determined that way.
 *
 * The human readable log message directly follows the message header. The
 * length of the message text is stored in the header, the stored message
 * is not terminated.
 *
 */

struct log {
	u64 ts_nsec;            /* timestamp in nanoseconds */
	u16 len;                /* length of entire record */
	u16 text_len;           /* length of text buffer */
	u16 dict_len;           /* length of dictionary buffer */
	u16 level;              /* syslog level + facility */
};

/*
 * The logbuf_lock protects kmsg buffer, indices, counters. It is also
 * used in interesting ways to provide interlocking in console_unlock();
 */
static DEFINE_RAW_SPINLOCK(logbuf_lock);

/* cpu currently holding logbuf_lock */
static volatile unsigned int logbuf_cpu = UINT_MAX;

#define LOG_LINE_MAX 1024

/* record buffer */
#define __LOG_BUF_LEN (1 << CONFIG_LOG_BUF_SHIFT)
static char __log_buf[__LOG_BUF_LEN];
static char *log_buf = __log_buf;
static u32 log_buf_len = __LOG_BUF_LEN;

/* index and sequence number of the first record stored in the buffer */
static u64 log_first_seq;
static u32 log_first_idx;

/* index and sequence number of the next record to store in the buffer */
static u64 log_next_seq;
static u32 log_next_idx;

/* the next printk record to read after the last 'clear' command */
static u64 clear_seq;
static u32 clear_idx;

/* the next printk record to read by syslog(READ) or /proc/kmsg */
static u64 syslog_seq;
static u32 syslog_idx;

/* human readable text of the record */
static char *log_text(const struct log *msg)
{
	return (char *)msg + sizeof(struct log);
}

/* optional key/value pair dictionary attached to the record */
static char *log_dict(const struct log *msg)
{
	return (char *)msg + sizeof(struct log) + msg->text_len;
}

/* get record by index; idx must point to valid msg */
static struct log *log_from_idx(u32 idx)
{
	struct log *msg = (struct log *)(log_buf + idx);

	/*
	* A length == 0 record is the end of buffer marker. Wrap around and
	* read the message at the start of the buffer.
	*/
	if (!msg->len)
		return (struct log *)log_buf;
	return msg;
}

/* get next record; idx must point to valid msg */
static u32 log_next(u32 idx)
{
	struct log *msg = (struct log *)(log_buf + idx);

	/* length == 0 indicates the end of the buffer; wrap */
	/*
	* A length == 0 record is the end of buffer marker. Wrap around and
	* read the message at the start of the buffer as *this* one, and
	* return the one after that.
	*/
	if (!msg->len) {
		msg = (struct log *)log_buf;
		return msg->len;
	}
	return idx + msg->len;
}

#if !defined(CONFIG_64BIT) || defined(CONFIG_HAVE_EFFICIENT_UNALIGNED_ACCESS)
#define LOG_ALIGN 4
#else
#define LOG_ALIGN 8
#endif

/* insert record into the buffer, discard old ones, update heads */
static void log_store(int facility, int level,
			const char *dict, u16 dict_len,
			const char *text, u16 text_len)
{
	struct log *msg;
	u32 size, pad_len;

	/* number of '\0' padding bytes to next message */
	size = sizeof(struct log) + text_len + dict_len;
	pad_len = (-size) & (LOG_ALIGN - 1);
	size += pad_len;

	while (log_first_seq < log_next_seq) {
		u32 free;

		if (log_next_idx > log_first_idx)
			free = max(log_buf_len - log_next_idx, log_first_idx);
		else
			free = log_first_idx - log_next_idx;

		if (free > size + sizeof(struct log))
			break;

		/* drop old messages until we have enough contiuous space */
		log_first_idx = log_next(log_first_idx);
		log_first_seq++;
	}

	if (log_next_idx + size + sizeof(struct log) >= log_buf_len) {
		/*
		* This message + an additional empty header does not fit
		* at the end of the buffer. Add an empty header with len == 0
		* to signify a wrap around.
		*/
		memset(log_buf + log_next_idx, 0, sizeof(struct log));
		log_next_idx = 0;
	}

	/* fill message */
	msg = (struct log *)(log_buf + log_next_idx);
	memcpy(log_text(msg), text, text_len);
	msg->text_len = text_len;
	memcpy(log_dict(msg), dict, dict_len);
	msg->dict_len = dict_len;
	msg->level = (facility << 3) | (level & 7);
	msg->ts_nsec = local_clock();
	memset(log_dict(msg) + dict_len, 0, pad_len);
	msg->len = sizeof(struct log) + text_len + dict_len + pad_len;

	/* insert message */
	log_next_idx += msg->len;
	log_next_seq++;
}

#ifdef CONFIG_KEXEC
void log_buf_kexec_setup(void)
{
	VMCOREINFO_SYMBOL(log_buf);
	VMCOREINFO_SYMBOL(log_buf_len);
	VMCOREINFO_SYMBOL(log_first_idx);
	VMCOREINFO_SYMBOL(log_next_idx);
}
#endif

static unsigned long __initdata new_log_buf_len;

static int __init log_buf_len_setup(char *str)
{
	unsigned size = memparse(str, &str);

	if (size)
		size = roundup_pow_of_two(size);
	if (size > log_buf_len)
		new_log_buf_len = size;

	return 0;
}
early_param("log_buf_len", log_buf_len_setup);

void __init setup_log_buf(int early)
{
	unsigned long flags;
	char *new_log_buf;
	int free;

	if (!new_log_buf_len)
		return;

	if (early) {
		unsigned long mem;

		mem = memblock_alloc(new_log_buf_len, PAGE_SIZE);
		if (!mem)
			return;
		new_log_buf = __va(mem);
	} else {
		new_log_buf = alloc_bootmem_nopanic(new_log_buf_len);
	}

	if (unlikely(!new_log_buf)) {
		pr_err("log_buf_len: %ld bytes not available\n",
			new_log_buf_len);
		return;
	}

	raw_spin_lock_irqsave(&logbuf_lock, flags);
	log_buf_len = new_log_buf_len;
	log_buf = new_log_buf;
	new_log_buf_len = 0;
	free = __LOG_BUF_LEN - log_next_idx;
	memcpy(log_buf, __log_buf, __LOG_BUF_LEN);
	raw_spin_unlock_irqrestore(&logbuf_lock, flags);

	pr_info("log_buf_len: %d\n", log_buf_len);
	pr_info("early log buf free: %d(%d%%)\n",
		free, (free * 100) / __LOG_BUF_LEN);
}

#ifdef CONFIG_BOOT_PRINTK_DELAY

static int boot_delay; 
static unsigned long long loops_per_msec;	

static int __init boot_delay_setup(char *str)
{
	unsigned long lpj;

	lpj = preset_lpj ? preset_lpj : 1000000;	
	loops_per_msec = (unsigned long long)lpj / 1000 * HZ;

	get_option(&str, &boot_delay);
	if (boot_delay > 10 * 1000)
		boot_delay = 0;

	pr_debug("boot_delay: %u, preset_lpj: %ld, lpj: %lu, "
		"HZ: %d, loops_per_msec: %llu\n",
		boot_delay, preset_lpj, lpj, HZ, loops_per_msec);
	return 1;
}
__setup("boot_delay=", boot_delay_setup);

static void boot_delay_msec(void)
{
	unsigned long long k;
	unsigned long timeout;

	if (boot_delay == 0 || system_state != SYSTEM_BOOTING)
		return;

	k = (unsigned long long)loops_per_msec * boot_delay;

	timeout = jiffies + msecs_to_jiffies(boot_delay);
	while (k) {
		k--;
		cpu_relax();
		if (time_after(jiffies, timeout))
			break;
		touch_nmi_watchdog();
	}
}
#else
static inline void boot_delay_msec(void)
{
}
#endif

#ifdef CONFIG_SECURITY_DMESG_RESTRICT
int dmesg_restrict = 1;
#else
int dmesg_restrict;
#endif

static int syslog_action_restricted(int type)
{
	if (dmesg_restrict)
		return 1;
	
	return type != SYSLOG_ACTION_READ_ALL && type != SYSLOG_ACTION_SIZE_BUFFER;
}

static int check_syslog_permissions(int type, bool from_file)
{
	if (from_file && type != SYSLOG_ACTION_OPEN)
		return 0;

	if (syslog_action_restricted(type)) {
		if (capable(CAP_SYSLOG))
			return 0;
		
		if (capable(CAP_SYS_ADMIN)) {
			printk_once(KERN_WARNING "%s (%d): "
				 "Attempt to access syslog with CAP_SYS_ADMIN "
				 "but no CAP_SYSLOG (deprecated).\n",
				 current->comm, task_pid_nr(current));
			return 0;
		}
		return -EPERM;
	}
	return 0;
}

#if defined(CONFIG_PRINTK_TIME)
static bool printk_time = 1;
#else
static bool printk_time;
#endif
module_param_named(time, printk_time, bool, S_IRUGO | S_IWUSR);

static int syslog_print_line(u32 idx, char *text, size_t size)
{
	struct log *msg;
	size_t len;

	msg = log_from_idx(idx);
	if (!text) {
		/* calculate length only */
		len = 3;

		if (msg->level > 9)
			len++;
		if (msg->level > 99)
			len++;

		if (printk_time)
			len += 15;

		len += msg->text_len;
		len++;
		return len;
	}

	len = sprintf(text, "<%u>", msg->level);

	if (printk_time) {
		unsigned long long t = msg->ts_nsec;
		unsigned long rem_ns = do_div(t, 1000000000);

		len += sprintf(text + len, "[%5lu.%06lu] ",
			(unsigned long) t, rem_ns / 1000);
	}

	if (len + msg->text_len > size)
		return -EINVAL;
	memcpy(text + len, log_text(msg), msg->text_len);
	len += msg->text_len;
	text[len++] = '\n';
	return len;
}

static int syslog_print(char __user *buf, int size)
{
	char *text;
	int len;

	text = kmalloc(LOG_LINE_MAX, GFP_KERNEL);
	if (!text)
		return -ENOMEM;

	raw_spin_lock_irq(&logbuf_lock);
	if (syslog_seq < log_first_seq) {
		/* messages are gone, move to first one */
		syslog_seq = log_first_seq;
		syslog_idx = log_first_idx;
	}
	len = syslog_print_line(syslog_idx, text, LOG_LINE_MAX);
	syslog_idx = log_next(syslog_idx);
	syslog_seq++;
	raw_spin_unlock_irq(&logbuf_lock);

	if (len > 0 && copy_to_user(buf, text, len))
		len = -EFAULT;

	kfree(text);
	return len;
}

static int syslog_print_all(char __user *buf, int size, bool clear)
{
	char *text;
	int len = 0;

	text = kmalloc(LOG_LINE_MAX, GFP_KERNEL);
	if (!text)
		return -ENOMEM;

	raw_spin_lock_irq(&logbuf_lock);
	if (buf) {
		u64 next_seq;
		u64 seq;
		u32 idx;

		if (clear_seq < log_first_seq) {
			/* messages are gone, move to first available one */
			clear_seq = log_first_seq;
			clear_idx = log_first_idx;
		}

		/*
		* Find first record that fits, including all following records,
		* into the user-provided buffer for this dump.
		*/
		seq = clear_seq;
		idx = clear_idx;
		while (seq < log_next_seq) {
			len += syslog_print_line(idx, NULL, 0);
			idx = log_next(idx);
			seq++;
		}
		seq = clear_seq;
		idx = clear_idx;
		while (len > size && seq < log_next_seq) {
			len -= syslog_print_line(idx, NULL, 0);
			idx = log_next(idx);
			seq++;
		}

		/* last message in this dump */
		next_seq = log_next_seq;

		len = 0;
		while (len >= 0 && seq < next_seq) {
			int textlen;

			textlen = syslog_print_line(idx, text, LOG_LINE_MAX);
			if (textlen < 0) {
				len = textlen;
				break;
			}
			idx = log_next(idx);
			seq++;

			raw_spin_unlock_irq(&logbuf_lock);
			if (copy_to_user(buf + len, text, textlen))
				len = -EFAULT;
			else
				len += textlen;
			raw_spin_lock_irq(&logbuf_lock);

			if (seq < log_first_seq) {
				/* messages are gone, move to next one */
				seq = log_first_seq;
				idx = log_first_idx;
			}
		}
	}

	if (clear) {
		clear_seq = log_next_seq;
		clear_idx = log_next_idx;
	}
	raw_spin_unlock_irq(&logbuf_lock);

	kfree(text);
	return len;
}

int do_syslog(int type, char __user *buf, int len, bool from_file)
{
	bool clear = false;
	static int saved_console_loglevel = -1;
	int error;

	error = check_syslog_permissions(type, from_file);
	if (error)
		goto out;

	error = security_syslog(type);
	if (error)
		return error;

	switch (type) {
	case SYSLOG_ACTION_CLOSE:	
		break;
	case SYSLOG_ACTION_OPEN:	
		break;
	case SYSLOG_ACTION_READ:	
		error = -EINVAL;
		if (!buf || len < 0)
			goto out;
		error = 0;
		if (!len)
			goto out;
		if (!access_ok(VERIFY_WRITE, buf, len)) {
			error = -EFAULT;
			goto out;
		}
		error = wait_event_interruptible(log_wait,
						syslog_seq != log_next_seq);
		if (error)
			goto out;
		error = syslog_print(buf, len);
		break;
	
	case SYSLOG_ACTION_READ_CLEAR:
		clear = true;
		/* FALL THRU */
	/* Read last kernel messages */
	case SYSLOG_ACTION_READ_ALL:
		error = -EINVAL;
		if (!buf || len < 0)
			goto out;
		error = 0;
		if (!len)
			goto out;
		if (!access_ok(VERIFY_WRITE, buf, len)) {
			error = -EFAULT;
			goto out;
		}
		error = syslog_print_all(buf, len, clear);
		break;
	
	case SYSLOG_ACTION_CLEAR:
		syslog_print_all(NULL, 0, true);
	/* Disable logging to console */
	case SYSLOG_ACTION_CONSOLE_OFF:
		if (saved_console_loglevel == -1)
			saved_console_loglevel = console_loglevel;
		console_loglevel = minimum_console_loglevel;
		break;
	
	case SYSLOG_ACTION_CONSOLE_ON:
		if (saved_console_loglevel != -1) {
			console_loglevel = saved_console_loglevel;
			saved_console_loglevel = -1;
		}
		break;
	
	case SYSLOG_ACTION_CONSOLE_LEVEL:
		error = -EINVAL;
		if (len < 1 || len > 8)
			goto out;
		if (len < minimum_console_loglevel)
			len = minimum_console_loglevel;
		console_loglevel = len;
		
		saved_console_loglevel = -1;
		error = 0;
		break;
	
	case SYSLOG_ACTION_SIZE_UNREAD:
		raw_spin_lock_irq(&logbuf_lock);
		if (syslog_seq < log_first_seq) {
			/* messages are gone, move to first one */
			syslog_seq = log_first_seq;
			syslog_idx = log_first_idx;
		}
		if (from_file) {
			/*
			* Short-cut for poll(/"proc/kmsg") which simply checks
			* for pending data, not the size; return the count of
			* records, not the length.
			*/
			error = log_next_idx - syslog_idx;
		} else {
			u64 seq;
			u32 idx;

			error = 0;
			seq = syslog_seq;
			idx = syslog_idx;
			while (seq < log_next_seq) {
				error += syslog_print_line(idx, NULL, 0);
				idx = log_next(idx);
				seq++;
			}
		}
		raw_spin_unlock_irq(&logbuf_lock);
		break;
	
	case SYSLOG_ACTION_SIZE_BUFFER:
		error = log_buf_len;
		break;
	default:
		error = -EINVAL;
		break;
	}
out:
	return error;
}

SYSCALL_DEFINE3(syslog, int, type, char __user *, buf, int, len)
{
	return do_syslog(type, buf, len, SYSLOG_FROM_CALL);
}

#ifdef	CONFIG_KGDB_KDB
void kdb_syslog_data(char *syslog_data[4])
{
	syslog_data[0] = log_buf;
	syslog_data[1] = log_buf + log_buf_len;
	syslog_data[2] = log_buf + log_first_idx;
	syslog_data[3] = log_buf + log_next_idx;
}
#endif	

static bool __read_mostly ignore_loglevel;

static int __init ignore_loglevel_setup(char *str)
{
	ignore_loglevel = 1;
	printk(KERN_INFO "debug: ignoring loglevel setting.\n");

	return 0;
}

early_param("ignore_loglevel", ignore_loglevel_setup);
module_param(ignore_loglevel, bool, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(ignore_loglevel, "ignore loglevel setting, to"
	"print all kernel messages to the console.");

/*
 * Call the console drivers, asking them to write out
 * log_buf[start] to log_buf[end - 1].
 * The console_lock must be held.
 */
static void call_console_drivers(int level, const char *text, size_t len)
{
	struct console *con;
	trace_console(text, 0, len, len);

	if (level >= console_loglevel && !ignore_loglevel)
		return;
	if (!console_drivers)
		return;

	for_each_console(con) {
		if (exclusive_console && con != exclusive_console)
			continue;
		if (!(con->flags & CON_ENABLED))
			continue;
		if (!con->write)
			continue;
		if (!cpu_online(smp_processor_id()) &&
			!(con->flags & CON_ANYTIME))
			continue;
		con->write(con, text, len);
	}
}


static void zap_locks(void)
{
	static unsigned long oops_timestamp;

	if (time_after_eq(jiffies, oops_timestamp) &&
			!time_after(jiffies, oops_timestamp + 30 * HZ))
		return;

	oops_timestamp = jiffies;

	debug_locks_off();
	
	raw_spin_lock_init(&logbuf_lock);
	
	sema_init(&console_sem, 1);
}

/* Check if we have any console registered that can be called early in boot. */
static int have_callable_console(void)
{
	struct console *con;

	for_each_console(con)
		if (con->flags & CON_ANYTIME)
			return 1;

	return 0;
}

/*
 * Can we actually use the console at this time on this cpu?
 *
 * Console drivers may assume that per-cpu resources have
 * been allocated. So unless they're explicitly marked as
 * being able to cope (CON_ANYTIME) don't call them until
 * this CPU is officially up.
 */
static inline int can_use_console(unsigned int cpu)
{
	return cpu_online(cpu) || have_callable_console();
}

static int console_trylock_for_printk(unsigned int cpu)
	__releases(&logbuf_lock)
{
	int retval = 0, wake = 0;

	if (console_trylock()) {
		retval = 1;

		if (!can_use_console(cpu)) {
			console_locked = 0;
			wake = 1;
			retval = 0;
		}
	}
	logbuf_cpu = UINT_MAX;
	if (wake)
		up(&console_sem);
	raw_spin_unlock(&logbuf_lock);
	return retval;
}

int printk_delay_msec __read_mostly;

static inline void printk_delay(void)
{
	if (unlikely(printk_delay_msec)) {
		int m = printk_delay_msec;

		while (m--) {
			mdelay(1);
			touch_nmi_watchdog();
		}
	}
}

asmlinkage int vprintk_emit(int facility, int level,
				const char *dict, size_t dictlen,
				const char *fmt, va_list args)
{
	static int recursion_bug;
	static char buf[LOG_LINE_MAX];
	static size_t buflen;
	static int buflevel;
	static char textbuf[LOG_LINE_MAX];
	char *text = textbuf;
	size_t textlen;
	unsigned long flags;
	int this_cpu;
	bool newline = false;
	bool cont = false;
	int printed_len = 0;

	boot_delay_msec();
	printk_delay();

	
	local_irq_save(flags);
	this_cpu = smp_processor_id();

	/*
	 * Ouch, printk recursed into itself!
	 */
	if (unlikely(logbuf_cpu == this_cpu)) {
		/*
		 * If a crash is occurring during printk() on this CPU,
		 * then try to get the crash message out but make sure
		 * we can't deadlock. Otherwise just return to avoid the
		 * recursion and return - but flag the recursion so that
		 * it can be printed at the next appropriate moment:
		 */
		if (!oops_in_progress && !lockdep_recursing(current)) {
			recursion_bug = 1;
			goto out_restore_irqs;
		}
		zap_locks();
	}

	lockdep_off();
	raw_spin_lock(&logbuf_lock);
	logbuf_cpu = this_cpu;

	if (recursion_bug) {
		static const char recursion_msg[] =
			"BUG: recent printk recursion!";

		recursion_bug = 0;
		printed_len += strlen(recursion_msg);
		/* emit KERN_CRIT message */
		log_store(0, 2, NULL, 0, recursion_msg, printed_len);

	}
	/*
	* The printf needs to come first; we need the syslog
	* prefix which might be passed-in as a parameter.
	*/
	textlen = vscnprintf(text, sizeof(textbuf), fmt, args);

	/* mark and strip a trailing newline */
	if (textlen && text[textlen-1] == '\n') {
		textlen--;
		newline = true;
	}

	/* strip syslog prefix and extract log level or flags */
	if (text[0] == '<' && text[1] && text[2] == '>') {
		switch (text[1]) {
		case '0' ... '7':
			if (level == -1)
				level = text[1] - '0';
			text += 3;
			textlen -= 3;
			break;
		case 'c':       /* KERN_CONT */
			cont = true;
		case 'd':       /* KERN_DEFAULT */
			text += 3;
			textlen -= 3;
			break;
		}
	}

	if (buflen && (!cont || dict)) {
		/* no continuation; flush existing buffer */
		log_store(facility, buflevel, NULL, 0, buf, buflen);
		printed_len += buflen;
		buflen = 0;
	}

	if (buflen == 0) {
		/* remember level for first message in the buffer */
		if (level == -1)
			buflevel = default_message_loglevel;
		else
			buflevel = level;
	}

	if (buflen || !newline) {
		/* append to existing buffer, or buffer until next message */
		if (buflen + textlen > sizeof(buf))
			textlen = sizeof(buf) - buflen;
		memcpy(buf + buflen, text, textlen);
		buflen += textlen;
	}

	if (newline) {
		/* end of line; flush buffer */
		if (buflen) {
			log_store(facility, buflevel,
				dict, dictlen, buf, buflen);
			printed_len += buflen;
			buflen = 0;
		} else {
			log_store(facility, buflevel,
				dict, dictlen, text, textlen);
			printed_len += textlen;
		}

	}

	/*
	* Try to acquire and then immediately release the console semaphore.
	* The release will print out buffers and wake up /dev/kmsg and syslog()
	* users.
	* The console_trylock_for_printk() function will release 'logbuf_lock'
	* regardless of whether it actually gets the console semaphore or not.
	*/
	if (console_trylock_for_printk(this_cpu))
		console_unlock();

	lockdep_on();
out_restore_irqs:
	local_irq_restore(flags);

	return printed_len;
}
EXPORT_SYMBOL(vprintk_emit);

asmlinkage int vprintk(const char *fmt, va_list args)
{
	return vprintk_emit(0, -1, NULL, 0, fmt, args);
}

EXPORT_SYMBOL(vprintk);
asmlinkage int printk_emit(int facility, int level,
				const char *dict, size_t dictlen,
				const char *fmt, ...)
{
	va_list args;
	int r;

	va_start(args, fmt);
	r = vprintk_emit(facility, level, dict, dictlen, fmt, args);
	va_end(args);

	return r;
}
EXPORT_SYMBOL(printk_emit);

/**
 * printk - print a kernel message
 * @fmt: format string
 *
 * This is printk(). It can be called from any context. We want it to work.
 *
 * We try to grab the console_lock. If we succeed, it's easy - we log the
 * output and call the console drivers.  If we fail to get the semaphore, we
 * place the output into the log buffer and return. The current holder of
 * the console_sem will notice the new output in console_unlock(); and will
 * send it to the consoles before releasing the lock.
 *
 * One effect of this deferred printing is that code which calls printk() and
 * then changes console_loglevel may break. This is because console_loglevel
 * is inspected when the actual printing occurs.
 *
 * See also:
 * printf(3)
 *
 * See the vsnprintf() documentation for format string extensions over C99.
 */
asmlinkage int printk(const char *fmt, ...)
{
	va_list args;
	int r;

#ifdef CONFIG_KGDB_KDB
	if (unlikely(kdb_trap_printk)) {
		va_start(args, fmt);
		r = vkdb_printf(fmt, args);
		va_end(args);
		return r;
	}
#endif
	va_start(args, fmt);
	r = vprintk_emit(0, -1, NULL, 0, fmt, args);
	va_end(args);

	return r;
}
EXPORT_SYMBOL(printk);

#else
static void call_console_drivers(int level, const char *text, size_t len)
{
}

#endif

static int __add_preferred_console(char *name, int idx, char *options,
				   char *brl_options)
{
	struct console_cmdline *c;
	int i;

	for (i = 0; i < MAX_CMDLINECONSOLES && console_cmdline[i].name[0]; i++)
		if (strcmp(console_cmdline[i].name, name) == 0 &&
			  console_cmdline[i].index == idx) {
				if (!brl_options)
					selected_console = i;
				return 0;
		}
	if (i == MAX_CMDLINECONSOLES)
		return -E2BIG;
	if (!brl_options)
		selected_console = i;
	c = &console_cmdline[i];
	strlcpy(c->name, name, sizeof(c->name));
	c->options = options;
#ifdef CONFIG_A11Y_BRAILLE_CONSOLE
	c->brl_options = brl_options;
#endif
	c->index = idx;
	return 0;
}
static int __init console_setup(char *str)
{
	char buf[sizeof(console_cmdline[0].name) + 4]; 
	char *s, *options, *brl_options = NULL;
	int idx;

#ifdef CONFIG_A11Y_BRAILLE_CONSOLE
	if (!memcmp(str, "brl,", 4)) {
		brl_options = "";
		str += 4;
	} else if (!memcmp(str, "brl=", 4)) {
		brl_options = str + 4;
		str = strchr(brl_options, ',');
		if (!str) {
			printk(KERN_ERR "need port name after brl=\n");
			return 1;
		}
		*(str++) = 0;
	}
#endif

	if (str[0] >= '0' && str[0] <= '9') {
		strcpy(buf, "ttyS");
		strncpy(buf + 4, str, sizeof(buf) - 5);
	} else {
		strncpy(buf, str, sizeof(buf) - 1);
	}
	buf[sizeof(buf) - 1] = 0;
	if ((options = strchr(str, ',')) != NULL)
		*(options++) = 0;
#ifdef __sparc__
	if (!strcmp(str, "ttya"))
		strcpy(buf, "ttyS0");
	if (!strcmp(str, "ttyb"))
		strcpy(buf, "ttyS1");
#endif
	for (s = buf; *s; s++)
		if ((*s >= '0' && *s <= '9') || *s == ',')
			break;
	idx = simple_strtoul(s, NULL, 10);
	*s = 0;

	__add_preferred_console(buf, idx, options, brl_options);
	console_set_on_cmdline = 1;
	return 1;
}
__setup("console=", console_setup);

int add_preferred_console(char *name, int idx, char *options)
{
	return __add_preferred_console(name, idx, options, NULL);
}

int update_console_cmdline(char *name, int idx, char *name_new, int idx_new, char *options)
{
	struct console_cmdline *c;
	int i;

	for (i = 0; i < MAX_CMDLINECONSOLES && console_cmdline[i].name[0]; i++)
		if (strcmp(console_cmdline[i].name, name) == 0 &&
			  console_cmdline[i].index == idx) {
				c = &console_cmdline[i];
				strlcpy(c->name, name_new, sizeof(c->name));
				c->name[sizeof(c->name) - 1] = 0;
				c->options = options;
				c->index = idx_new;
				return i;
		}
	
	return -1;
}

bool console_suspend_enabled = 1;
EXPORT_SYMBOL(console_suspend_enabled);

static int __init console_suspend_disable(char *str)
{
	console_suspend_enabled = 0;
	return 1;
}
__setup("no_console_suspend", console_suspend_disable);

int suspend_console_deferred;
module_param_named(
	suspend_console_deferred, suspend_console_deferred, int, S_IRUGO | S_IWUSR | S_IWGRP
);

module_param_named(console_suspend, console_suspend_enabled,
		bool, S_IRUGO | S_IWUSR);
MODULE_PARM_DESC(console_suspend, "suspend console during suspend"
	" and hibernate operations");

void suspend_console(void)
{
	if (!console_suspend_enabled)
		return;
	printk("Suspending console(s) (use no_console_suspend to debug)\n");
	console_lock();
	console_suspended = 1;
	up(&console_sem);
}

void resume_console(void)
{
	if (!console_suspend_enabled)
		return;
	down(&console_sem);
	console_suspended = 0;
	console_unlock();
}

static void console_flush(struct work_struct *work)
{
	console_lock();
	console_unlock();
}

static DECLARE_WORK(console_cpu_notify_work, console_flush);

static int console_cpu_notify(struct notifier_block *self,
	unsigned long action, void *hcpu)
{
	switch (action) {
	case CPU_DEAD:
	case CPU_DOWN_FAILED:
	case CPU_UP_CANCELED:
		console_lock();
		console_unlock();
		break;
	case CPU_ONLINE:
	case CPU_DYING:
		
		if (!console_trylock())
			schedule_work(&console_cpu_notify_work);
		else
			console_unlock();
	}
	return NOTIFY_OK;
}

void console_lock(void)
{
	BUG_ON(in_interrupt());
	down(&console_sem);
	if (console_suspended)
		return;
	console_locked = 1;
	console_may_schedule = 1;
}
EXPORT_SYMBOL(console_lock);

int console_trylock(void)
{
	if (down_trylock(&console_sem))
		return 0;
	if (console_suspended) {
		up(&console_sem);
		return 0;
	}
	console_locked = 1;
	console_may_schedule = 0;
	return 1;
}
EXPORT_SYMBOL(console_trylock);

int is_console_locked(void)
{
	return console_locked;
}

/*
 * Delayed printk version, for scheduler-internal messages:
 */
#define PRINTK_BUF_SIZE		512

#define PRINTK_PENDING_WAKEUP	0x01
#define PRINTK_PENDING_SCHED	0x02

static DEFINE_PER_CPU(int, printk_pending);
static DEFINE_PER_CPU(char [PRINTK_BUF_SIZE], printk_sched_buf);

void printk_tick(void)
{
	if (__this_cpu_read(printk_pending)) {
		int pending = __this_cpu_xchg(printk_pending, 0);
		if (pending & PRINTK_PENDING_SCHED) {
			char *buf = __get_cpu_var(printk_sched_buf);
			printk(KERN_WARNING "[sched_delayed] %s", buf);
		}
		if (pending & PRINTK_PENDING_WAKEUP)
			wake_up_interruptible(&log_wait);
	}
}

int printk_needs_cpu(int cpu)
{
	if (cpu_is_offline(cpu))
		printk_tick();
	return __this_cpu_read(printk_pending);
}

void wake_up_klogd(void)
{
	if (waitqueue_active(&log_wait))
		this_cpu_or(printk_pending, PRINTK_PENDING_WAKEUP);
}
/* the next printk record to write to the console */
static u64 console_seq;
static u32 console_idx;

/**
 * console_unlock - unlock the console system
 *
 * Releases the console_lock which the caller holds on the console system
 * and the console driver list.
 *
 * While the console_lock was held, console output may have been buffered
 * by printk().  If this is the case, console_unlock(); emits
 * the output prior to releasing the lock.
 *
 * If there is output waiting, we wake it /dev/kmsg and syslog() users.
 *
 * console_unlock(); may be called from any context.
 */
void console_unlock(void)
{
	static u64 seen_seq;
	unsigned long flags;
	bool wake_klogd = false;
	bool retry;

	if (console_suspended) {
		up(&console_sem);
		return;
	}

	console_may_schedule = 0;

again:
	for (;;) {
		struct log *msg;
		static char text[LOG_LINE_MAX];
		size_t len;
		int level;
		raw_spin_lock_irqsave(&logbuf_lock, flags);
		if (seen_seq != log_next_seq) {
			wake_klogd = true;
			seen_seq = log_next_seq;
		}

		if (console_seq < log_first_seq) {
			/* messages are gone, move to first one */
			console_seq = log_first_seq;
			console_idx = log_first_idx;
		}

		if (console_seq == log_next_seq)
			break;

		msg = log_from_idx(console_idx);
		level = msg->level & 7;
		len = msg->text_len;
		if (len+1 >= sizeof(text))
			len = sizeof(text)-1;
		memcpy(text, log_text(msg), len);
		text[len++] = '\n';

		console_idx = log_next(console_idx);
		console_seq++;

		raw_spin_unlock(&logbuf_lock);
		stop_critical_timings();	/* don't trace print latency */
		call_console_drivers(level, text, len);
		start_critical_timings();
		local_irq_restore(flags);
	}
	console_locked = 0;

	
	if (unlikely(exclusive_console))
		exclusive_console = NULL;

	raw_spin_unlock(&logbuf_lock);

	up(&console_sem);

	raw_spin_lock(&logbuf_lock);
	retry = console_seq != log_next_seq;
	raw_spin_unlock_irqrestore(&logbuf_lock, flags);

	if (retry && console_trylock())
		goto again;

	if (wake_klogd)
		wake_up_klogd();
}
EXPORT_SYMBOL(console_unlock);

void __sched console_conditional_schedule(void)
{
	if (console_may_schedule)
		cond_resched();
}
EXPORT_SYMBOL(console_conditional_schedule);

void console_unblank(void)
{
	struct console *c;

	if (oops_in_progress) {
		if (down_trylock(&console_sem) != 0)
			return;
	} else
		console_lock();

	console_locked = 1;
	console_may_schedule = 0;
	for_each_console(c)
		if ((c->flags & CON_ENABLED) && c->unblank)
			c->unblank();
	console_unlock();
}

struct tty_driver *console_device(int *index)
{
	struct console *c;
	struct tty_driver *driver = NULL;

	console_lock();
	for_each_console(c) {
		if (!c->device)
			continue;
		driver = c->device(c, index);
		if (driver)
			break;
	}
	console_unlock();
	return driver;
}

void console_stop(struct console *console)
{
	console_lock();
	console->flags &= ~CON_ENABLED;
	console_unlock();
}
EXPORT_SYMBOL(console_stop);

void console_start(struct console *console)
{
	console_lock();
	console->flags |= CON_ENABLED;
	console_unlock();
}
EXPORT_SYMBOL(console_start);

static int __read_mostly keep_bootcon;

static int __init keep_bootcon_setup(char *str)
{
	keep_bootcon = 1;
	printk(KERN_INFO "debug: skip boot console de-registration.\n");

	return 0;
}

early_param("keep_bootcon", keep_bootcon_setup);

void register_console(struct console *newcon)
{
	int i;
	unsigned long flags;
	struct console *bcon = NULL;

	if (console_drivers && newcon->flags & CON_BOOT) {
		
		for_each_console(bcon) {
			if (!(bcon->flags & CON_BOOT)) {
				printk(KERN_INFO "Too late to register bootconsole %s%d\n",
					newcon->name, newcon->index);
				return;
			}
		}
	}

	if (console_drivers && console_drivers->flags & CON_BOOT)
		bcon = console_drivers;

	if (preferred_console < 0 || bcon || !console_drivers)
		preferred_console = selected_console;

	if (newcon->early_setup)
		newcon->early_setup();

	if (preferred_console < 0) {
		if (newcon->index < 0)
			newcon->index = 0;
		if (newcon->setup == NULL ||
		    newcon->setup(newcon, NULL) == 0) {
			newcon->flags |= CON_ENABLED;
			if (newcon->device) {
				newcon->flags |= CON_CONSDEV;
				preferred_console = 0;
			}
		}
	}

	for (i = 0; i < MAX_CMDLINECONSOLES && console_cmdline[i].name[0];
			i++) {
		BUILD_BUG_ON(sizeof(console_cmdline[i].name) != sizeof(newcon->name));
		if (strcmp(console_cmdline[i].name, newcon->name) != 0)
			continue;
		if (newcon->index >= 0 &&
		    newcon->index != console_cmdline[i].index)
			continue;
		if (newcon->index < 0)
			newcon->index = console_cmdline[i].index;
#ifdef CONFIG_A11Y_BRAILLE_CONSOLE
		if (console_cmdline[i].brl_options) {
			newcon->flags |= CON_BRL;
			braille_register_console(newcon,
					console_cmdline[i].index,
					console_cmdline[i].options,
					console_cmdline[i].brl_options);
			return;
		}
#endif
		if (newcon->setup &&
		    newcon->setup(newcon, console_cmdline[i].options) != 0)
			break;
		newcon->flags |= CON_ENABLED;
		newcon->index = console_cmdline[i].index;
		if (i == selected_console) {
			newcon->flags |= CON_CONSDEV;
			preferred_console = selected_console;
		}
		break;
	}

	if (!(newcon->flags & CON_ENABLED))
		return;

	if (bcon && ((newcon->flags & (CON_CONSDEV | CON_BOOT)) == CON_CONSDEV))
		newcon->flags &= ~CON_PRINTBUFFER;

	console_lock();
	if ((newcon->flags & CON_CONSDEV) || console_drivers == NULL) {
		newcon->next = console_drivers;
		console_drivers = newcon;
		if (newcon->next)
			newcon->next->flags &= ~CON_CONSDEV;
	} else {
		newcon->next = console_drivers->next;
		console_drivers->next = newcon;
	}
	if (newcon->flags & CON_PRINTBUFFER) {
		raw_spin_lock_irqsave(&logbuf_lock, flags);
		console_seq = syslog_seq;
		console_idx = syslog_idx;
		raw_spin_unlock_irqrestore(&logbuf_lock, flags);
		exclusive_console = newcon;
	}
	console_unlock();
	console_sysfs_notify();

	if (bcon &&
	    ((newcon->flags & (CON_CONSDEV | CON_BOOT)) == CON_CONSDEV) &&
	    !keep_bootcon) {
		printk(KERN_INFO "console [%s%d] enabled, bootconsole disabled\n",
			newcon->name, newcon->index);
		for_each_console(bcon)
			if (bcon->flags & CON_BOOT)
				unregister_console(bcon);
	} else {
		printk(KERN_INFO "%sconsole [%s%d] enabled\n",
			(newcon->flags & CON_BOOT) ? "boot" : "" ,
			newcon->name, newcon->index);
	}
}
EXPORT_SYMBOL(register_console);

int unregister_console(struct console *console)
{
        struct console *a, *b;
	int res = 1;

#ifdef CONFIG_A11Y_BRAILLE_CONSOLE
	if (console->flags & CON_BRL)
		return braille_unregister_console(console);
#endif

	console_lock();
	if (console_drivers == console) {
		console_drivers=console->next;
		res = 0;
	} else if (console_drivers) {
		for (a=console_drivers->next, b=console_drivers ;
		     a; b=a, a=b->next) {
			if (a == console) {
				b->next = a->next;
				res = 0;
				break;
			}
		}
	}

	if (console_drivers != NULL && console->flags & CON_CONSDEV)
		console_drivers->flags |= CON_CONSDEV;

	console_unlock();
	console_sysfs_notify();
	return res;
}
EXPORT_SYMBOL(unregister_console);

static int __init printk_late_init(void)
{
	struct console *con;

	for_each_console(con) {
		if (!keep_bootcon && con->flags & CON_BOOT) {
			printk(KERN_INFO "turn off boot console %s%d\n",
				con->name, con->index);
			unregister_console(con);
		}
	}
	hotcpu_notifier(console_cpu_notify, 0);
	return 0;
}
late_initcall(printk_late_init);

#if defined CONFIG_PRINTK

int printk_deferred(const char *fmt, ...)
{
	unsigned long flags;
	va_list args;
	char *buf;
	int r;

	local_irq_save(flags);
	buf = __get_cpu_var(printk_sched_buf);

	va_start(args, fmt);
	r = vsnprintf(buf, PRINTK_BUF_SIZE, fmt, args);
	va_end(args);

	__this_cpu_or(printk_pending, PRINTK_PENDING_SCHED);
	local_irq_restore(flags);

	return r;
}

DEFINE_RATELIMIT_STATE(printk_ratelimit_state, 5 * HZ, 10);

int __printk_ratelimit(const char *func)
{
	return ___ratelimit(&printk_ratelimit_state, func);
}
EXPORT_SYMBOL(__printk_ratelimit);

bool printk_timed_ratelimit(unsigned long *caller_jiffies,
			unsigned int interval_msecs)
{
	if (*caller_jiffies == 0
			|| !time_in_range(jiffies, *caller_jiffies,
					*caller_jiffies
					+ msecs_to_jiffies(interval_msecs))) {
		*caller_jiffies = jiffies;
		return true;
	}
	return false;
}
EXPORT_SYMBOL(printk_timed_ratelimit);

static DEFINE_SPINLOCK(dump_list_lock);
static LIST_HEAD(dump_list);

int kmsg_dump_register(struct kmsg_dumper *dumper)
{
	unsigned long flags;
	int err = -EBUSY;

	
	if (!dumper->dump)
		return -EINVAL;

	spin_lock_irqsave(&dump_list_lock, flags);
	
	if (!dumper->registered) {
		dumper->registered = 1;
		list_add_tail_rcu(&dumper->list, &dump_list);
		err = 0;
	}
	spin_unlock_irqrestore(&dump_list_lock, flags);

	return err;
}
EXPORT_SYMBOL_GPL(kmsg_dump_register);

int kmsg_dump_unregister(struct kmsg_dumper *dumper)
{
	unsigned long flags;
	int err = -EINVAL;

	spin_lock_irqsave(&dump_list_lock, flags);
	if (dumper->registered) {
		dumper->registered = 0;
		list_del_rcu(&dumper->list);
		err = 0;
	}
	spin_unlock_irqrestore(&dump_list_lock, flags);
	synchronize_rcu();

	return err;
}
EXPORT_SYMBOL_GPL(kmsg_dump_unregister);
static bool always_kmsg_dump;
module_param_named(always_kmsg_dump, always_kmsg_dump, bool, S_IRUGO | S_IWUSR);


void kmsg_dump(enum kmsg_dump_reason reason)
{
	u64 idx;
	struct kmsg_dumper *dumper;
	const char *s1, *s2;
	unsigned long l1, l2;
	unsigned long flags;

	if ((reason > KMSG_DUMP_OOPS) && !always_kmsg_dump)
		return;

	raw_spin_lock_irqsave(&logbuf_lock, flags);
	if (syslog_seq < log_first_seq)
		idx = syslog_idx;
	else
		idx = log_first_idx;

	if (idx > log_next_idx) {
		s1 = log_buf;
		l1 = log_next_idx;
		s2 = log_buf + idx;
		l2 = log_buf_len - idx;
	} else {
		s1 = "";
		l1 = 0;

		s2 = log_buf + idx;
		l2 = log_next_idx - idx;
	}
	raw_spin_unlock_irqrestore(&logbuf_lock, flags);

	rcu_read_lock();
	list_for_each_entry_rcu(dumper, &dump_list, list)
		dumper->dump(dumper, reason, s1, l1, s2, l2);
	rcu_read_unlock();
}
#endif
