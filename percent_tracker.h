// version: 1
#include <stdint.h>
#include <sys/time.h>

typedef struct
{
	struct timeval t0;
	uint64_t progress_capt;
	float progress;
	uint64_t time_ms_est;
	uint64_t time_ms_pass;
} progress_tracker_t;

#ifndef PERC_TRACKER_SCALER
#define PERC_TRACKER_SCALER 10000.0f
#endif

#define PERCENT_TRACKER_INIT(TRK) \
	gettimeofday(&TRK.t0, NULL);  \
	TRK.progress_capt = 0;        \
	TRK.progress = 0;             \
	TRK.time_ms_est = 0;          \
	TRK.time_ms_pass = 0;

#define PERCENT_TRACKER_TRACK(TR, val, FUN)                                                                    \
	if(TR.progress_capt < (uint64_t)roundf(PERC_TRACKER_SCALER * (float)(val)))                                \
	{                                                                                                          \
		TR.progress_capt = (uint64_t)roundf(PERC_TRACKER_SCALER * (float)(val));                               \
		TR.progress = (float)TR.progress_capt / (uint64_t)PERC_TRACKER_SCALER;                                 \
		struct timeval t1;                                                                                     \
		gettimeofday(&t1, NULL);                                                                               \
		TR.time_ms_pass = (uint64_t)((t1.tv_sec - TR.t0.tv_sec) * 1000 + (t1.tv_usec - TR.t0.tv_usec) / 1000); \
		TR.time_ms_est = (uint64_t)((float)TR.time_ms_pass / TR.progress);                                     \
		FUN;                                                                                                   \
	}

// ===== EXAMPLE =====
//	progress_tracker_t tr;
//	PERCENT_TRACKER_INIT(tr);
//	for(uint32_t i = 0; i < 100; i++)
//	{
//		PERCENT_TRACKER_TRACK(tr, (float)i / (float)(100), { printf("\r%.1f%% | pass: %lld sec | est: %lld sec\t\t\t",
//																	100.0 * tr.progress,
//																	tr.time_ms_pass / 1000,
//																	tr.time_ms_est / 1000); });
//		fflush(stdout);
//		usleep(200000);
//	}