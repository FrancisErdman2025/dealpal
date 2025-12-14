// content-script.js - DealPal Amazon product extraction (robust)
(function() {
  function extract() {
    try {
      // Product title
      const title = document.querySelector('#productTitle')?.innerText?.trim() || document.title;

      // Price detection: cover all common Amazon patterns
      const priceSelectors = [
        '#priceblock_ourprice',
        '#priceblock_dealprice',
        '#priceblock_saleprice',
        '.a-price .a-offscreen',
        '#tp_price_block_total_price_ww', // some subscription prices
        '#price_inside_buybox'
      ];

      let priceText = null;
      for (let selector of priceSelectors) {
        const el = document.querySelector(selector);
        if (el && el.innerText.trim()) {
          priceText = el.innerText.trim();
          break;
        }
      }

      const numericPrice = priceText ? parseFloat(priceText.replace(/[^\d\.]/g, '')) : null;

      const productInfo = {
        title: title || '',
        priceText: priceText || null,
        price: numericPrice,
        url: location.href,
        ts: Date.now()
      };

      // Send to popup/background
      chrome.runtime.sendMessage({ type: 'PRODUCT_INFO', payload: productInfo });

    } catch (e) {
      console.error('DealPal content script extract error', e);
      chrome.runtime.sendMessage({
        type: 'PRODUCT_INFO',
        payload: { title: document.title || '', url: location.href, ts: Date.now() }
      });
    }
  }

  // Run immediately
  extract();
})();
