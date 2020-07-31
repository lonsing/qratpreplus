/*
 This file is part of QRATPre+.

 Copyright 2019
 Florian Lonsing, Stanford University, USA.

 Copyright 2018 
 Florian Lonsing, Vienna University of Technology, Austria.

 QRATPre+ is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or (at
 your option) any later version.

 QRATPre+ is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with QRATPre+.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <signal.h>
#include <stdlib.h>
#include <ctype.h>
#include <dirent.h>
#include <assert.h>
#include "qratpreplus.h"

struct QRATPrePlusApp
{
  QRATPrePlus *qr;
  struct 
  {
    int print_usage;
    int print_version;
    int verbosity;
    int print_formula;
    char *in_filename;
  } options;
};

typedef struct QRATPrePlusApp QRATPrePlusApp;

/* -------------------- START: Helper macros -------------------- */

#define VERSION                                                   \
  "QRATPre+ 2.0\n"                                                \
  "Copyright 2019 Florian Lonsing, Stanford University, USA.\n"   \
  "Copyright 2018 Florian Lonsing, TU Wien, Austria.\n"           \
  "This is free software; see LICENSE for copying conditions.\n"  \
  "There is NO WARRANTY, to the extent permitted by law.\n"

#define USAGE \
"usage: ./qratplus [options] input-formula [timeout]\n"\
"\n"\
"  - 'input-formula' is a file in QDIMACS format (default: stdin)\n"\
"  - '[timeout]' is an optional timeout in seconds\n"\
"  - '[options]' is any combination of the following:\n\n"\
"    -h, --help                    print this usage information and exit\n"\
"    -v                            increase verbosity level incrementally (default: 0)\n"\
"    --version                     print version information and exit\n"\
"    --print-formula               print simplified formula to stdout\n" \
"    --no-ble                      disable blocked literal elimination (BLE) \n"\
"    --no-qratu                    disable QRAT-based elimination of universal literals (QRATU)\n" \
"    --no-qbce                     disable blocked clause elimination (QBCE)\n"\
"    --no-qat                      disable asymmetric tautology (QAT) checks of clauses\n"\
"    --no-qrate                    disable QRAT-based elimination of clauses (QRATE)\n" \
"    --no-eabs                     disable prefix abstraction\n"\
"    --no-eabs-improved-nesting    disable improved prefix abstraction\n"\
"    --soft-time-limit=<n>         enforce soft time limit in <n> seconds\n"\
"    --permute                     randomly permute clause lists between iterations\n" \
"    --formula-stats               compute formula statistics before and after preprocessing\n" \
"    --seed=<n>                    in combination with '--permute': random seed <n>(default: 0)\n" \
"    --ignore-outermost-vars       do not eliminate clauses or universal literals in clauses that contain\n"\
"                                    a literal from the outermost (i.e. first) quantifier block\n" \
"\n"

/* Macro to print message and abort. */
#define ABORT_APP(cond,msg)						 \
  do {                                                                   \
    if (cond)                                                            \
      {                                                                  \
        fprintf (stderr, "[QRATPREPLUS] %s at line %d: %s\n", __func__, \
                 __LINE__, msg);                                         \
        fflush (stderr);                                                 \
        abort();                                                         \
      }                                                                  \
  } while (0)

/* -------------------- END: Helper macros -------------------- */

/* Print error message. */
static void
print_abort_err (char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  fprintf (stderr, "qratplus: ");
  va_start (list, msg);
  vfprintf (stderr, msg, list);
  va_end (list);
  fflush (stderr);
  abort ();
}

static int
isnumstr (char *str)
{
  /* Empty string is not considered as number-string. */
  if (!*str)
    return 0;
  char *p;
  for (p = str; *p; p++)
    {
      if (!isdigit (*p))
        return 0;
    }
  return 1;
}

/* Parse command line arguments to set options accordingly. Run the program
   with '-h' or '--help' to print usage information. */
static char *
parse_cmd_line_options (QRATPrePlusApp * qra, int argc, char **argv)
{
  char *result = 0;
  int opt_cnt;
  for (opt_cnt = 1; opt_cnt < argc; opt_cnt++)
    {
      char *opt_str = argv[opt_cnt];
      if (!strcmp (opt_str, "-h") || !strcmp (opt_str, "--help"))
        {
          qra->options.print_usage = 1;
        }
      else if (!strcmp (opt_str, "--version"))
        {
          qra->options.print_version = 1;
        }
      else if (!strncmp (opt_str, "--print-formula", strlen ("--print-formula")))
        {
          qra->options.print_formula = 1;
        }
      else if (!strcmp (opt_str, "-v"))
        {
          qra->options.verbosity++;
          /* Handle error strings returned from library function in
             'result'. */
          if ((result = qratpreplus_configure (qra->qr, opt_str)))
            return result;
        }
      else if (!strncmp (opt_str, "--", strlen ("--")) || isnumstr (opt_str))
        {
          /* Catch library options, assuming that each of them begin
             with '--'. 'isnumstr' is used to pass an integer value as
             a time out. Handle error strings returned from library
             function in 'result'. */
          if ((result = qratpreplus_configure (qra->qr, opt_str)))
            return result;
        }
      else if (!qra->options.in_filename)
        {
          qra->options.in_filename = opt_str;
          /* Check of file exists. */
          DIR *dir;
          if ((dir = opendir (qra->options.in_filename)) != NULL)
            {
              closedir (dir);
              print_abort_err ("input file '%s' is a directory!\n\n",
                               qra->options.in_filename);
            }
          FILE *input_file = fopen (qra->options.in_filename, "r");
          if (!input_file)
            {
              print_abort_err ("could not open input file '%s'!\n\n",
                               qra->options.in_filename);
            }
          else
            {
              fclose(input_file);
            }
        }
      else
        print_abort_err ("Input file already given at '%s'!\n\n",
                         qra->options.in_filename);      
    }
  return result;
}

/* Set signal handler. */
static void
sig_handler (int sig)
{
  fprintf (stderr, "\n\n SIG RECEIVED\n\n");
  signal (sig, SIG_DFL);
  raise (sig);
}

/* Set signal handler. */
static void
sigalrm_handler (int sig)
{
  fprintf (stderr, "\n\n SIGALRM RECEIVED\n\n");
  signal (sig, SIG_DFL);
  raise (sig);
}

/* Set signal handler. */
static void
set_signal_handlers (void)
{
  signal (SIGINT, sig_handler);
  signal (SIGTERM, sig_handler);
  signal (SIGALRM, sigalrm_handler);
  signal (SIGXCPU, sigalrm_handler);
}

static void
print_usage ()
{
  fprintf (stdout, USAGE);
}

static void
print_version ()
{
  fprintf (stdout, VERSION);
}


int
main (int argc, char **argv)
{
  QRATPrePlusApp qra;
  memset (&qra, 0, sizeof (QRATPrePlusApp));

  int result = 0;
  /* Initialize QRATPrePlus object. */
  qra.qr = qratpreplus_create ();
    
  char *err_str = parse_cmd_line_options (&qra, argc, argv);
  if (err_str)
    print_abort_err ("error in command line: '%s'\n", err_str);
    
  set_signal_handlers ();

  if (qra.options.print_usage || qra.options.print_version)
    {
      if (qra.options.print_usage)
        print_usage ();
      else
        print_version ();

      qratpreplus_delete (qra.qr);
      return result;
    }

 /* Import QDIMACS formula. */
  qratpreplus_add_formula (qra.qr, qra.options.in_filename);

  /* Preprocess formula. */
  qratpreplus_preprocess (qra.qr);

  /* Print formula to stdout. */
  if (qra.options.print_formula)
    qratpreplus_print_formula (qra.qr, stdout);

  if (qra.options.verbosity >= 1)
    {
      qratpreplus_print_stats (qra.qr, stderr);
    }

  qratpreplus_delete (qra.qr);

  return result;
}

