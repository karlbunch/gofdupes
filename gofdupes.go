//
// gofdupes Copyright (c) 2014 Karl Bunch <bunchk at karlbunch.com>
//
// A Go implementation of Adrian Lopez's FDUPES 1.5.1 https://code.google.com/p/fdupes/source/browse/trunk/fdupes.c
//
// Note a newer version exists at: https://github.com/adrianlopezroche/fdupes
//
// STEPS:
//
// Pass 1 - Gather all files + partial CRC (first PARTIAL_MD5_SIZE btyes)
// Pass 2 - Discard anything that doesn't have more then 1 partial sum match
// Pass 3 - Full sum compare of files
//
//
/* From original C program: https://code.google.com/p/fdupes/source/browse/trunk/fdupes.c

   FDUPES Copyright (c) 1999-2002 Adrian Lopez

   Permission is hereby granted, free of charge, to any person
   obtaining a copy of this software and associated documentation files
   (the "Software"), to deal in the Software without restriction,
   including without limitation the rights to use, copy, modify, merge,
   publish, distribute, sublicense, and/or sell copies of the Software,
   and to permit persons to whom the Software is furnished to do so,
   subject to the following conditions:
   The above copyright notice and this permission notice shall be
   included in all copies or substantial portions of the Software.
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
   OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
   IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
   CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
   TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
   SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. */

package main

import (
	"bytes"
	"crypto/md5"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
)

const VERSION = "0.0.2"

var (
	BUILDTIME      = "unknown" // Makefile will update this via build ldflags
	flag_recurse   = flag.Bool("recurse", false, "\n\tfor every directory given follow subdirectories encountered within\n")
	flag_symlinks  = flag.Bool("symlinks", false, "\n\tfollow symlinked directories\n")
	flag_hardlinks = flag.Bool("hardlinks", false, "\n\tnormally, when two or more files point to the same disk area they are treated as non-duplicates; this option will change this behavior\n")
	flag_noempty   = flag.Bool("noempty", false, "\n\texclude zero-length files from consideration\n")
	flag_nohidden  = flag.Bool("nohidden", true, "\n\texclude hidden files from consideration\n")
	flag_omitfirst = flag.Bool("omitfirst", false, "\n\tomit the first file in each set of matches\n")
	flag_sameline  = flag.Bool("sameline", false, "\n\tlist each set of matches on a single line\n")
	flag_size      = flag.Bool("size", false, "\n\tshow size of duplicate files\n")
	flag_summarize = flag.Bool("summarize", false, "\n\tsummarize dupe information\n")
	flag_quiet     = flag.Bool("quiet", false, "\n\thide progress indicator\n")
	flag_debug     = flag.Bool("debug", false, "\n\tturn on verbose debug output\n")
	flag_delete    = flag.Bool("delete", false, "\n\tprompt user for files to preserve and delete all\n\t"+
		"others; important: under particular circumstances,\n\t"+
		"data may be lost when using this option together\n\t"+
		"with --symlinks, or when specifying a\n\t"+
		"particular directory more than once; refer to the\n\t"+
		"fdupes documentation for additional information\n")
	flag_noprompt = flag.Bool("noprompt", false, "\n\twhen used together with --delete, preserve the first file in each set of duplicates and delete the others without prompting the user\n")
	flag_version  = flag.Bool("version", false, "\n\tdisplay version and exit\n")
)

// Setup aliases for long args
func init() {
	flag.BoolVar(flag_recurse, "r", *flag_recurse, "See: --recurse\n")
	flag.BoolVar(flag_symlinks, "s", *flag_symlinks, "See: --symlinks\n")
	flag.BoolVar(flag_hardlinks, "H", *flag_hardlinks, "See: --hardlinks\n")
	flag.BoolVar(flag_noempty, "n", *flag_noempty, "See: --noempty\n")
	flag.BoolVar(flag_omitfirst, "f", *flag_omitfirst, "See: --omitfirst\n")
	flag.BoolVar(flag_sameline, "1", *flag_sameline, "See: --sameline\n")
	flag.BoolVar(flag_size, "S", *flag_size, "See: --size\n")
	flag.BoolVar(flag_summarize, "m", *flag_summarize, "See: --summarize\n")
	flag.BoolVar(flag_quiet, "q", *flag_quiet, "See: --quiet\n")
	flag.BoolVar(flag_delete, "d", *flag_delete, "See: --delete\n")
	flag.BoolVar(flag_noprompt, "N", *flag_noprompt, "See: --noprompt\n")
	flag.BoolVar(flag_version, "v", *flag_version, "See: --version\n")
	flag.BoolVar(flag_debug, "x", *flag_debug, "See: --debug\n")
}

type hash_t [md5.Size]byte

type file_t struct {
	path       string
	info       os.FileInfo
	partialSum hash_t
	fullSum    hash_t
	err        error
}

type hashMap_t map[hash_t][]file_t

type hashList_t []hash_t

type ByHash hashList_t

func (a ByHash) Len() int           { return len(a) }
func (a ByHash) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a ByHash) Less(i, j int) bool { return bytes.Compare(a[i][:], a[j][:]) < 0 }

func NewFile(initPath string) file_t {
	f := new(file_t)

	f.path = initPath
	f.info, f.err = os.Lstat(f.path)

	return *f
}

const PARTIAL_MD5_SIZE = 4096

func treeWalker(done <-chan struct{}, roots []string) (<-chan string, <-chan error) {
	paths := make(chan string)
	errchan := make(chan error, len(roots))

	var wg sync.WaitGroup

	for _, root := range roots {
		wg.Add(1)
		go func(treeRoot string) {
			defer wg.Done()

			if *flag_debug {
				fmt.Fprintf(os.Stderr, "\r** Pass 1 - Start walking %s  \n", treeRoot)
			}
			errchan <- filepath.Walk(treeRoot, func(path string, info os.FileInfo, err error) error {
				if err != nil {
					if os.IsPermission(err) || os.IsNotExist(err) {
						fmt.Fprintf(os.Stderr, "\n%s\n", err)
						return nil
					} else {
						return err
					}
				}

				if info.IsDir() {
					if !*flag_recurse ||
						(*flag_nohidden && info.Name()[0] == '.') {
						return filepath.SkipDir
					}
				}

				if !info.Mode().IsRegular() ||
					(*flag_noempty && info.Size() == 0) ||
					(*flag_nohidden && info.Name()[0] == '.') {
					return nil
				}

				select {
				case paths <- path:
				case <-done:
					return errors.New("treeWalker cancelled")
				}
				return nil
			})
			if *flag_debug {
				fmt.Fprintf(os.Stderr, "\r** Pass 1 - Done walking %s\n", treeRoot)
			}
		}(root)
	}

	go func() {
		wg.Wait()
		if *flag_debug {
			fmt.Fprintf(os.Stderr, "\r** Pass 1 - Walkers done\n")
		}
		close(paths)
	}()

	return paths, errchan
}

// partialSum reads path names from paths and sends digests of the
// first PARTIAL_MD5_SIZE bytes corresponding files to result until
// either paths or done is closed.
func partialSum(done <-chan struct{}, paths <-chan string, result chan<- file_t) {
	for path := range paths {
		thisFile := NewFile(path)

		if fh, err := os.Open(path); err != nil {
			if os.IsPermission(err) || os.IsNotExist(err) {
				continue
			}
			thisFile.err = err
		} else {
			hasher := md5.New()
			io.CopyN(hasher, fh, PARTIAL_MD5_SIZE)
			fh.Close()
			copy(thisFile.partialSum[:], hasher.Sum(nil))
		}

		select {
		case result <- thisFile:
		case <-done:
			return
		}
	}
}

// Same as partialSum except the entire file is used
func fullSum(done <-chan struct{}, files <-chan file_t, result chan<- file_t) {
	for file := range files {
		if fh, err := os.Open(file.path); err != nil {
			if os.IsPermission(err) || os.IsNotExist(err) {
				continue
			}
			file.err = err
		} else {
			hasher := md5.New()
			io.Copy(hasher, fh)
			fh.Close()
			copy(file.fullSum[:], hasher.Sum(nil))
		}

		select {
		case result <- file:
		case <-done:
			return
		}
	}
}

func GoFdupes_Pass1(roots []string, numDigesters int) (hashMap_t, error) {
	done := make(chan struct{})
	defer close(done)

	paths, errc := treeWalker(done, roots)

	files := make(chan file_t)

	// Start a fixed number of goroutines to do pass 1 sums
	var wg sync.WaitGroup
	wg.Add(numDigesters)

	for i := 0; i < numDigesters; i++ {
		go func() {
			partialSum(done, paths, files)
			wg.Done()
		}()
	}

	// Watch for end of wait group then close files channel
	go func() {
		wg.Wait()
		close(files)
	}()

	count := 0

	if !*flag_quiet {
		start_tm := time.Now()
		progress := 0
		tick := time.Tick(time.Millisecond * 250)

		go func() {
			for {
				select {
				case <-tick:
					delta_tm := time.Since(start_tm).Seconds() + 0.0001
					ps := float64(count) / delta_tm
					fmt.Fprintf(os.Stderr, "\r** Pass 1 - Scanning files %c [%d] %.02f/s", "-\\|/"[progress], count, ps)
					progress++
					progress %= 4
				case <-done:
					delta_tm := time.Since(start_tm).Seconds() + 0.0001
					ps := float64(count) / delta_tm
					fmt.Fprintf(os.Stderr, "\r** Pass 1 - Scanned %d files in %.02f second(s) (%.02f/s)\n", count, delta_tm, ps)
					return
				}
			}
		}()
	}

	partialSums := make(hashMap_t)

handleFiles:
	for file := range files {
		count++
		if file.err != nil {
			return nil, file.err
		}

		if t, ok := partialSums[file.partialSum]; ok && !*flag_hardlinks {
			// Check for hardlinked file
			for _, f := range t {
				if os.SameFile(file.info, f.info) {
					if *flag_debug {
						fmt.Fprintf(os.Stderr, "\n%s HARDLINK TO %s\n", file.path, f.path)
					}
					continue handleFiles
				}
			}
		}

		partialSums[file.partialSum] = append(partialSums[file.partialSum], file)
	}

	// Check whether the Walk failed.
	if err := <-errc; err != nil {
		return nil, err
	}

	return partialSums, nil
}

func GoFdupes_Pass2(potentialDupes hashMap_t, numDigesters int) (hashMap_t, error) {
	needFullSum := make(chan file_t)
	haveFullSum := make(chan file_t)
	done := make(chan struct{})
	defer close(done)

	// Start a fixed number of goroutines to do pass 2 sums
	var wg sync.WaitGroup
	wg.Add(numDigesters)

	for i := 0; i < numDigesters; i++ {
		go func() {
			fullSum(done, needFullSum, haveFullSum)
			wg.Done()
		}()
	}

	// Watch for end of wait group then close channel
	go func() {
		wg.Wait()
		close(haveFullSum)
	}()

	count := 0
	bytes := int64(0)

	if !*flag_quiet {
		start_tm := time.Now()
		progress := 0
		tick := time.Tick(time.Millisecond * 250)

		total_files := 0
		total_bytes := int64(0)

		for _, entry := range potentialDupes {
			total_files += len(entry)
			for _, file := range entry {
				total_bytes += file.info.Size()
			}
		}

		go func() {
			for {
				select {
				case <-tick:
					delta_tm := time.Since(start_tm).Seconds() + 0.0001
					ps := float64(count) / delta_tm
					bps := float64(bytes) / delta_tm
					eta := (total_bytes - bytes) / int64(bps)
					fmt.Fprintf(os.Stderr, "\r** Pass 2 - Full sum files %c [%d] %.02f/s %.02f/MBs %v    \r", "-\\|/"[progress], total_files-count, ps, bps/1000/1000, time.Duration(eta)*time.Second)
					progress++
					progress %= 4
				case <-done:
					delta_tm := time.Since(start_tm).Seconds() + 0.0001
					ps := float64(count) / delta_tm
					mbps := float64(bytes) / delta_tm / 1000 / 1000
					fmt.Fprintf(os.Stderr, "\r** Pass 2 - Summed %d files in %.02f second(s) (%.02f/s %.02f/MBs)\n", count, delta_tm, ps, mbps)
					return
				}
			}
		}()
	}

	// Send potentialDupes files to the work queue
	go func() {
		for _, entry := range potentialDupes {
			for _, file := range entry {
				needFullSum <- file
			}
		}
		close(needFullSum)
	}()

	fullSums := make(hashMap_t)

	for file := range haveFullSum {
		count++
		bytes += file.info.Size()
		if file.err != nil {
			return nil, file.err
		}
		fullSums[file.fullSum] = append(fullSums[file.fullSum], file)
	}

	return fullSums, nil
}

func GoFdupes(roots []string, numDigesters int) (hashMap_t, error) {
	partialSums, p1_err := GoFdupes_Pass1(roots, numDigesters)

	if p1_err != nil {
		fmt.Printf("\n** Pass 1 - Failed: %s\n", p1_err)
		return nil, p1_err
	}

	if *flag_debug {
		fmt.Fprintf(os.Stderr, "\r** Pass 1 - Found %d unique partial sums\n", len(partialSums))
	}

	// Discard anything that doesn't have more then one match
	potentialDupes := make(hashMap_t)
	count := 0

	for key, entry := range partialSums {
		if len(entry) > 1 {
			potentialDupes[key] = entry
			count += len(entry)
		}
	}

	if *flag_debug {
		fmt.Fprintf(os.Stderr, "\r** Pass 1 - Found %d partial sum duplicates on %d files\n", len(potentialDupes), count)
	}

	fullSums, p2_err := GoFdupes_Pass2(potentialDupes, numDigesters)

	if p2_err != nil {
		fmt.Printf("\n** Pass 2 - Failed: %s\n", p2_err)
		return nil, p2_err
	}

	// Discard anything that doesn't have more then one match
	dupes := make(hashMap_t)
	count = 0

	for key, entry := range fullSums {
		if len(entry) > 1 {
			dupes[key] = entry
			count += len(entry)
		}
	}

	if *flag_debug {
		fmt.Fprintf(os.Stderr, "\r** Pass 2 - Found %d full sum duplicates on %d files\n", len(dupes), count)
	}

	return dupes, p2_err
}

func Ouput_Style_new(hashes hashList_t, dupes hashMap_t) {
	for _, hash := range hashes {
		var files = dupes[hash]

		fmt.Printf("%x %x\n", files[0].partialSum, files[0].fullSum)

		paths := make([]string, 0, len(files))
		for _, file := range files {
			paths = append(paths, file.path)
		}
		sort.Strings(paths)
		for n, path := range paths {
			flag1 := " "
			if n > 0 && os.SameFile(files[n-1].info, files[n].info) {
				flag1 = "!"
			}
			flag2 := " "
			if n > 0 && files[n-1].path == files[n].path {
				flag2 = "="
			}
			fmt.Printf("%s%s  %4d) %s\n", flag1, flag2, n+1, path)
		}
		fmt.Printf("\n")
	}
}

func cleanupFilePath(path string) string {
	var escapechars = [...]string{"\\", " ", "\t"}

	for _, ch := range escapechars {
		path = strings.Replace(path, ch, "\\"+ch, -1)
	}

	return path
}

func Ouput_Style_fdupes_sameline(hashes hashList_t, dupes hashMap_t) {
	for _, hash := range hashes {
		var files = dupes[hash]
		paths := make([]string, 0, len(files))
		for _, file := range files {
			paths = append(paths, file.path)
		}
		sort.Strings(paths)
		if *flag_size {
			fmt.Printf("%d bytes each:\n", files[0].info.Size())
		}
		for n, path := range paths {
			if !*flag_omitfirst || n != 0 {
				fmt.Printf("%s ", cleanupFilePath(path))
			}
		}
		fmt.Printf("\n")
	}
}

func Ouput_Style_fdupes(hashes hashList_t, dupes hashMap_t) {
	for _, hash := range hashes {
		var files = dupes[hash]
		paths := make([]string, 0, len(files))
		for _, file := range files {
			paths = append(paths, file.path)
		}
		sort.Strings(paths)
		if *flag_size {
			fmt.Printf("%d bytes each:\n", files[0].info.Size())
		}
		for n, path := range paths {
			if !*flag_omitfirst || n != 0 {
				fmt.Printf("%s\n", path)
			}
		}
		fmt.Printf("\n")
	}
}

func OutputSummary(dupes hashMap_t) {
	if len(dupes) == 0 {
		fmt.Printf("No duplicates found.\n\n")
		return
	}

	total_files := int64(0)
	total_bytes := float64(0)

	for _, dupe := range dupes {
		for _, f := range dupe {
			total_bytes += float64(f.info.Size())
			total_files++
		}
	}

	if total_bytes < 1024.0 {
		fmt.Printf("%d duplicate files (in %d sets), occupying %.0f bytes.\n\n", total_files, len(dupes), total_bytes)
	} else if total_bytes <= (1000.0 * 1000.0) {
		fmt.Printf("%d duplicate files (in %d sets), occupying %.1f kilobytes\n\n", total_files, len(dupes), total_bytes/1000.0)
	} else {
		fmt.Printf("%d duplicate files (in %d sets), occupying %.1f megabytes\n\n", total_files, len(dupes), total_bytes/(1000.0*1000.0))
	}
}

func main() {
	flag.Parse()

	if *flag_version {
		fmt.Printf("Version %s (%s)\n", VERSION, BUILDTIME)
		os.Exit(1)
	}

	if *flag_symlinks {
		// TODO should we implement this? Seems really dangerous, not sure what original use cases where
		os.Stderr.Write([]byte("symlink traversal not implemented\n"))
		os.Exit(1)
	}

	if *flag_summarize && *flag_delete {
		os.Stderr.Write([]byte("options --summarize and --delete are not compatible\n"))
		os.Exit(1)
	}

	if *flag_delete {
		// TODO implement this!  need to make 100% certain files are exact matches etc before delete
		os.Stderr.Write([]byte("--delete not implemented yet.\n"))
		os.Exit(1)
	}

	// TODO command arg?
	runtime.GOMAXPROCS(int(float64(runtime.NumCPU()) * 1.25))

	dupes, err := GoFdupes(flag.Args(), runtime.GOMAXPROCS(0))

	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}

	if *flag_summarize {
		OutputSummary(dupes)
		os.Exit(0)
	}

	var hashes = make(hashList_t, 0, len(dupes))

	for key, _ := range dupes {
		hashes = append(hashes, key)
	}

	sort.Sort(ByHash(hashes))

	if *flag_sameline {
		Ouput_Style_fdupes_sameline(hashes, dupes)
	} else {
		Ouput_Style_fdupes(hashes, dupes)
	}

	os.Exit(0)
}
